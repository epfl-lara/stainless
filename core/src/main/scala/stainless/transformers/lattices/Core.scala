package stainless
package transformers
package lattices

import inox.solvers
import inox.utils.LruCache

trait Core extends Definitions { ocbsl =>
  val opts: solvers.PurityOptions

  import trees._
  import symbols.{given, _}
  import Opaques.{given, _}
  import Purity._
  import scala.collection.mutable // A bit ironic that we import mutable stuff right after "Purity"...

  private val codemapThreshold = 150000

  private val sig2codeMap = mutable.Map.empty[Signature, Code]
  private val code2sigMap = mutable.Map.empty[Code, Signature]
  private val codeTpeMap = mutable.Map.empty[Code, Type]

  private val fnBodyMap = mutable.Map.empty[Identifier, CodeRes]

  private var varIdCounter: Int = 0
  private val varId2Var = mutable.Map.empty[VarId, Variable]
  private val var2VarId = mutable.Map.empty[Variable, VarId]

  private val codePurityInst = new CodePurity

  // Not for sparing allocations, but for sparing key strokes :p
  final val BoolTy: Type = BooleanType()

  final val falseSig: Signature = Signature(Label.Lit(BooleanLiteral(false)), Seq.empty)
  final val trueSig: Signature = Signature(Label.Lit(BooleanLiteral(true)), Seq.empty)
  final val unitSig: Signature = Signature(Label.Lit(UnitLiteral()), Seq.empty)
  final val falseCode: Code = codeOfSig(falseSig, BoolTy)
  final val trueCode: Code = codeOfSig(trueSig, BoolTy)
  final val unitCode: Code = codeOfSig(unitSig, UnitType())
  final val zero: Code = codeOfIntLit(0, IntegerType())
  final val one: Code = codeOfIntLit(1, IntegerType())
  final val two: Code = codeOfIntLit(2, IntegerType())

  private val plugCacheThreshold = 10000
  private val pluggedMap = mutable.Map.empty[(CodeRes, Ctxs, Env), (Occurrences, Code)]
  private val unplugMap = mutable.Map.empty[(Code, Env), Map[Ctxs, (CodeRes, Occurrences)]]

  private val negCodeCacheThreshold = 10000
  private val negCodeCache = mutable.Map.empty[Code, Code]

  // An lru and not a map cache because we do necessarily need the cached computation for the entire VC simplification process
  private val code2linCombLru = new inox.utils.LruCache[Code, LinComb](1000)
  private val linComb2codeLru = new inox.utils.LruCache[LinComb, Code](1000)

  final inline val debug = false

  final inline def assert(cond: => Boolean): Unit =
    inline if (debug) Predef.assert(cond)

  final inline def assert(cond: => Boolean, msg: => String): Unit =
    inline if (debug) Predef.assert(cond, msg)

  enum Retirement {
    case KeepGoing
    case WellDeserved(fnPurityCache: Map[Identifier, Boolean])
  }

  // If the codemap gets too large, we should just retire this instance and create a fresh one.
  final def shouldRetire(): Retirement =
    if (code2sigMap.size <= codemapThreshold) Retirement.KeepGoing
    else Retirement.WellDeserved(codePurityInst.functionsPurity())

  final def setFunctionPurityCache(fnPurityCache: Map[Identifier, Boolean]): Unit =
    codePurityInst.setFunctionPurityCache(fnPurityCache)

  def clearCaches(): Unit = {
    if (pluggedMap.size > plugCacheThreshold) {
      pluggedMap.clear()
      unplugMap.clear()
    }
    if (negCodeCache.size > negCodeCacheThreshold) {
      negCodeCache.clear()
    }
    occOfInst.clearCaches()
    codePurityInst.clearCaches()
  }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Various simple ADTs

  case class Env(nesting: LambdaNesting, forceBinding: Boolean) {
    def inc: Env = Env(nesting.inc, forceBinding)
    def incIf(lab: Label.LambdaLike): Env = Env(nesting.incIf(lab), forceBinding)
  }

  object Env {
    def empty: Env = Env(LambdaNesting(0), false)
  }

  case class LambdaNesting(level: Int) {
    require(level >= 0)

    def inAnyLambda: Boolean = level > 0
    def inc: LambdaNesting = LambdaNesting(level + 1)
    def incIf(lab: Label.LambdaLike): LambdaNesting =
      if (lab.isLambda) inc else this
  }

  enum OccurrenceKind {
    case Expanded
    case Applied
  }

  enum Occurrence {
    case Zero
    case Once(inCtxs: Ctxs, nesting: LambdaNesting, kind: OccurrenceKind)
    case Many

    def ++(that: Occurrence): Occurrence = (this, that) match {
      case (Zero, _) => that
      case (_, Zero) => this
      case _ => Many
    }

    def isZero: Boolean = this match {
      case Zero => true
      case _ => false
    }

    def isOnce: Boolean = this match {
      case Once(_, _, _) => true
      case _ => false
    }

    def isMany: Boolean = this match {
      case Many => true
      case _ => false
    }

    def nonZero: Boolean = !isZero

    override def toString: String = this match {
      case Zero => "Zero"
      case Once(_, _, _) => "Once"
      case Many => "Many"
    }
  }

  case class Occurrences(c2u: Map[Code, Occurrence]) {
    def hasLambda: Boolean = c2u.keys.exists(isLambda)

    def apply(c: Code): Occurrence = c2u.getOrElse(c, Occurrence.Zero)

    def +(c: Code, occ: Occurrence): Occurrences = this ++ Occurrences(Map(c -> occ))

    def ++(that: Occurrences): Occurrences = Occurrences((c2u.keySet ++ that.c2u.keySet)
      .map(c => c -> (this (c) ++ that(c))).toMap)

    def setTo(c: Code, o: Occurrence): Occurrences = Occurrences(c2u + (c -> o))

    def setAsApplied(c: Code): Occurrences = {
      this(c) match {
        case Occurrence.Once(inCtxs, nesting, _) => Occurrences(c2u + (c -> Occurrence.Once(inCtxs, nesting, OccurrenceKind.Applied)))
        case _ => this
      }
    }

    def -(c: Code): Occurrences = Occurrences(c2u - c)

    def manyied: Occurrences = Occurrences(c2u.map {
      case (c, Occurrence.Zero) => (c, Occurrence.Zero)
      case (c, _) => c -> Occurrence.Many
    })

    def allSuffixes(ctxs: Ctxs): Boolean = c2u.values.forall {
      case Occurrence.Once(inCtxs, _, _) => ctxs.isPrefixOf(inCtxs)
      case _ => true
    }

    def withInlinedOccurrences(newInCtxs: Ctxs, nesting: LambdaNesting)(using env: Env): Occurrences = {
      assert(env.nesting.level <= nesting.level)
      Occurrences(c2u.map {
        case (c, Occurrence.Once(prevInCtxs, nesting2, kind)) =>
          assert(env.nesting.level <= nesting2.level)
          val nbNestedLambdas = nesting2.level - env.nesting.level
          val ctxs = prevInCtxs.movedAfter(newInCtxs)
          c -> Occurrence.Once(ctxs, LambdaNesting(nesting.level + nbNestedLambdas), kind)
        case (c, occ) => c -> occ
      })
    }

    def withRemovedBinding(bound: Code): Occurrences = withRemovedBindings(Set(bound))

    def withRemovedBindings(bound: Set[Code]): Occurrences = Occurrences(c2u.map {
      case (c, Occurrence.Once(inCtxs, nesting, kind)) =>
        c -> Occurrence.Once(inCtxs.withRemovedBindings(bound), nesting, kind)
      case (c, occ) => c -> occ
    })
  }

  object Occurrences {
    def empty: Occurrences = Occurrences(Map.empty)

    def of(c: Code)(using env: Env, ctxs: Ctxs): Occurrences = {
      assert(CodeRes.isTerminal(c))
      if (isLit(c)) Occurrences.empty
      else {
        val impures = ctxs.impureParts
        Occurrences(Map(c -> Occurrence.Once(impures, env.nesting, OccurrenceKind.Expanded)))
      }
    }
  }

  case class LetValSubst(subst: Map[Variable, Code]) {
    def apply(v: Variable): Code = {
      assert(subst.contains(v))
      subst(v)
    }

    def get(v: Variable): Option[Code] = subst.get(v)

    def +(t: (Variable, Code)): LetValSubst = {
      assert(!subst.contains(t._1))
      LetValSubst(subst + t)
    }
  }

  object LetValSubst {
    def empty: LetValSubst = LetValSubst(Map.empty)
  }

  case class LinComb(terms: Map[Code, BigInt], cst: BigInt, tpe: Type) {
    def +(that: LinComb): LinComb = {
      assert(tpe == that.tpe)
      val resTerms = (terms.keySet ++ that.terms.keySet).foldLeft(Map.empty[Code, BigInt]) {
        case (acc, c) => (terms.get(c), that.terms.get(c)) match {
          case (Some(l1), Some(l2)) =>
            val l = l1 + l2
            if (l == 0) acc
            else acc + (c -> l)
          case (Some(l1), None) => acc + (c -> l1)
          case (None, Some(l2)) => acc + (c -> l2)
          case (None, None) => sys.error("how come")
        }
      }
      LinComb(resTerms, cst + that.cst, tpe)
    }
    def -(that: LinComb): LinComb = this + -that
    def unary_- : LinComb = LinComb(terms.view.mapValues(-_).toMap, -cst, tpe)
  }
  object LinComb {
    def empty(tpe: Type): LinComb = LinComb(Map.empty, 0, tpe)
  }
  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Ctxs and CodeRes

  enum Ctx {
    case BoundDef(terminal: Code)
    case AssumeLike(lab: Label.AssumeLike, predTerminal: Code)
    case Assumed(cond: Code) // From branches etc.

    lazy val hc: Int = this match {
      case Ctx.BoundDef(t) => java.util.Objects.hash(t)
      case Ctx.AssumeLike(l, p) => java.util.Objects.hash(l, p)
      case Ctx.Assumed(c) => java.util.Objects.hash(c)
    }
    override def hashCode(): Int = hc

    def isBoundDef(c: Code): Boolean = this match {
      case Ctx.BoundDef(c2) => c == c2
      case _ => false
    }
  }

  case class Ctxs(ctxs: Seq[Ctx]) {
    import Ctxs._
    assert(
      ctxs.forall {
        case Ctx.BoundDef(terminal) => !isLitOrVar(terminal)
        case _ => true
      }, "Var or lit binding")
    assert(
      ctxs.collect {
        case bd@Ctx.BoundDef(_) => bd
      }.groupBy(_.terminal).forall(_._2.size == 1),
      "Multiple binding of same code")

    lazy val hc: Int = java.util.Objects.hash(ctxs)
    override def hashCode(): Int = hc

    lazy val allConds: Seq[Code] = ctxs.foldLeft(Seq.empty[Code]) {
      case (acc, Ctx.AssumeLike(lab, c)) if !lab.isDecreases => acc :+ c
      case (acc, Ctx.Assumed(c)) => acc :+ c
      case (acc, _) => acc
    }
    lazy val allCondsSet: Set[Code] = allConds.toSet

    lazy val bound: Seq[Code] = ctxs.collect {
      case Ctx.BoundDef(c) => c
    }

    private val impurePartsCache = mutable.Map.empty[Env, Ctxs]

    def impureParts(using env: Env): Ctxs = {
      if (env.forceBinding) return this

      impurePartsCache.getOrElseUpdate(env, {
        Ctxs(ctxs.foldLeft((Seq.empty[Ctx], Seq.empty[Ctx])) {
          case ((prevCtxs, impureCtxs), assm@(Ctx.Assumed(_) | Ctx.AssumeLike(_, _))) => (prevCtxs :+ assm, impureCtxs :+ assm)
          case ((prevCtxs, impureCtxs), b@Ctx.BoundDef(t)) =>
            val p = codePurity(t)(using env, Ctxs(prevCtxs))
            if (p.isPure) (prevCtxs :+ b, impureCtxs)
            else (prevCtxs :+ b, impureCtxs :+ b)
        }._2)
      })
    }

    def withReplacedPrefix(oldPrefix: Ctxs, newPrefix: Ctxs): Ctxs = {
      assert(oldPrefix.isPrefixOf(this))
      val suffix = ctxs.drop(oldPrefix.size)
      suffix.foldLeft(newPrefix)(_.addCtx(_))
    }

    def addExtraWithoutAssumed(suffix: Ctxs): Ctxs = {
      assert(this.isPrefixOf(suffix))
      val (common, extra) = suffix.ctxs.splitAt(this.size)
      Ctxs(extra.foldLeft(common) {
        case (acc, ctx@(Ctx.BoundDef(_) | Ctx.AssumeLike(_, _))) => acc :+ ctx
        case (acc, Ctx.Assumed(_)) => acc
      })
    }

    def addCtx(ctx: Ctx): Ctxs = ctx match {
      case bd@Ctx.BoundDef(t) =>
        if (isLitVarOrBoundDef(t)) this
        else Ctxs(ctxs :+ bd)
      case a@Ctx.Assumed(cond) =>
        if (cond == trueCode || allCondsSet.contains(cond)) this
        else Ctxs(ctxs :+ a)
      case a@Ctx.AssumeLike(kind, pred) =>
        if (pred == trueCode || (!kind.isDecreases && allCondsSet.contains(pred))) this
        else Ctxs(ctxs :+ a)
    }

    def addCtxs(that: Ctxs): Ctxs = that.ctxs.foldLeft(this)(_.addCtx(_))

    def size: Int = ctxs.size

    def lastOption: Option[Ctx] = ctxs.lastOption

    def pop: Option[(Ctxs, Ctx)] = {
      if (ctxs.isEmpty) None
      else Some((Ctxs(ctxs.init), ctxs.last))
    }

    def withRemovedBinding(c: Code): Ctxs = withRemovedBindings(Set(c))

    def withRemovedBindings(cs: Set[Code]): Ctxs = {
      Ctxs(ctxs.filterNot {
        case Ctx.BoundDef(c) => cs(c)
        case _ => false
      })
    }

    def withRemovedBindingIfNoOccurrence(prefix: Ctxs, cs: Seq[Code]): (Ctxs, Boolean) = {
      cs.foldLeft((this, true)) {
        case ((ctxs, allRm), c) =>
          val (newCtxs, rm) = ctxs.withRemovedBindingIfNoOccurrence(prefix, c)
          (newCtxs, allRm && rm)
      }
    }

    def withRemovedBindingIfNoOccurrence(prefix: Ctxs, c: Code): (Ctxs, Boolean) = {
      assert(prefix.isPrefixOf(this))
      val ix = ctxs.indexOf(Ctx.BoundDef(c))
      if (ix < 0) (this, true)
      else if (ix < prefix.ctxs.size) (this, false)
      else {
        val (before, after) = ctxs.splitAt(ix)
        val noOccurrence = after.tail.forall {
          case Ctx.Assumed(_) => true
          case Ctx.BoundDef(df) => occurrencesOf(df)(using Env.empty, Ctxs.empty)(c).isZero
          case Ctx.AssumeLike(_, pred) => occurrencesOf(pred)(using Env.empty, Ctxs.empty)(c).isZero
        }
        if (noOccurrence) (Ctxs(before ++ after.tail), true)
        else (this, false)
      }
    }

    def occurrences(inCtxs: Ctxs)(using Env): Occurrences = {
      assert(inCtxs.isPrefixOf(this))
      if (this.ctxs.isEmpty) Occurrences.empty
      else CodeRes(unitCode, this).selfPlugged(inCtxs)._1
    }

    def movedAfter(after: Ctxs): Ctxs = {
      val common = this.ctxs.zip(after.ctxs).takeWhile { case (slf, after) => slf == after }.map(_._1)
      val suffixThis = this.ctxs.drop(common.size)
      val suffixAfter = after.ctxs.drop(common.size)
      val merged = common ++ suffixAfter ++ suffixThis
      Ctxs(merged)
    }

    // In short: we plug until we get to inCtxs
    def plugged(inCtxs: Ctxs, terminal: Code)(using env: Env): (Occurrences, Code, CodeRes) = {
      assert(inCtxs.isPrefixOf(this))
      assert(CodeRes.isTerminal(terminal))

      def rec(curr: Ctxs, u: Occurrences, c: Code, partialCr: PartialCodeRes): (Occurrences, Code, CodeRes) = {
        assert(inCtxs.isPrefixOf(curr))
        assert(curr.isPrefixOf(this))
        if (curr.ctxs.size == inCtxs.ctxs.size) {
          val minCr = CodeRes(partialCr.terminal, Ctxs(inCtxs.ctxs ++ partialCr.suffixCtxs))
          (u, c, minCr)
        } else {
          assert(curr.ctxs.nonEmpty)
          val (prev, toPlug) = curr.pop.get
          val (u2, c2, partialCr2) = Ctxs.plugCtx(prev, toPlug, u, c, partialCr)
          rec(prev, u2, c2, partialCr2)
        }
      }

      val occ = occurrencesOf(terminal)(using env, this)
      rec(this, occ, terminal, PartialCodeRes(terminal, Seq.empty))
    }

    def isBoundDef(c: Code): Boolean = ctxs.exists(_.isBoundDef(c))

    def takeUntilDefined(c: Code): Ctxs = {
      Ctxs(ctxs.takeWhile {
        case Ctx.BoundDef(c2) => c != c2
        case _ => true
      })
    }

    def isLitVarOrBoundDef(c: Code): Boolean = isLitOrVar(c) || isBoundDef(c)

    def isPrefixOf(that: Ctxs): Boolean = ocbsl.isPrefixOf(this.ctxs, that.ctxs)

    def addBoundDef(df: Code)(using env: Env): Ctxs = {
      assert(CodeRes.isTerminal(df))
      assert(terminalPartsBound(df))

      if (isLitOrVar(df) || isBoundDef(df)) this
      else Ctxs(ctxs :+ Ctx.BoundDef(df))
    }

    def addBoundDefs(dfs: Seq[Code])(using env: Env): Ctxs = dfs.foldLeft(this)(_.addBoundDef(_))

    def terminalPartsBound(terminal: Code): Boolean = {
      assert(CodeRes.isTerminal(terminal))
      code2sig(terminal) match {
        case Signature(Label.IfExpr, Seq(cond, _, _)) => isLitVarOrBoundDef(cond)
        case Signature(Label.MatchExpr(_), scrut +: _) => isLitVarOrBoundDef(scrut)
        case Signature(Label.Passes(_), scrut +: _) => isLitVarOrBoundDef(scrut)
        case Signature(Label.Or, fst +: _) => isLitVarOrBoundDef(fst)
        case Signature(Label.Not, Seq(e)) => isLitVarOrBoundDef(e)
        case Signature(_: (Label.Ensuring.type | Label.LambdaLike), _) => true
        case Signature(_, args) => args.forall(isLitVarOrBoundDef)
      }
    }

    def withCond(cond: Code): Ctxs = {
      if (cond == trueCode || allCondsSet.contains(cond)) this
      else Ctxs(ctxs :+ Ctx.Assumed(cond))
    }

    def withNegatedCond(cond: Code): Ctxs = withCond(negCodeOf(cond))

    def withConds(conds: Seq[Code]): Ctxs =
      conds.foldLeft(this)((acc, c) => acc.withCond(c))

    def withAssumeLike(kind: Label.AssumeLike, pred: Code): Ctxs = {
      assert(CodeRes.isTerminal(pred))
      assert(isLitVarOrBoundDef(pred))
      if (pred == trueCode || (!kind.isDecreases && allCondsSet.contains(pred))) this
      else Ctxs(ctxs :+ Ctx.AssumeLike(kind, pred))
    }
  }

  object Ctxs {

    private case class PartialCodeRes(terminal: Code, suffixCtxs: Seq[Ctx]) {
      // As we are going "bottom to top", we concatenate "backwards"
      def +:(ctx: Ctx): PartialCodeRes = PartialCodeRes(terminal, ctx +: suffixCtxs)
    }

    def empty: Ctxs = new Ctxs(Seq.empty)

    private def plugCtx(prev: Ctxs, toPlug: Ctx, u: Occurrences, c: Code, partialCr: PartialCodeRes)
                       (using env: Env): (Occurrences, Code, PartialCodeRes) = {
      if (Thread.interrupted()) throw new InterruptedException()

      def inlineAppliedLambda(cLam: Code, in: Code): (Occurrences, Code, PartialCodeRes) = {
        val Signature(Label.Lambda(params), Seq(body)) = code2sig(cLam): @unchecked
        object inliner extends CodeTransformer {
          override type Extra = Unit

          override def transformImpl(c: Code, repl: Map[Code, Code], extra: Unit)
                                    (using env: Env, ctxs: Ctxs): CodeRes = code2sig(c) match {
            case Signature(Label.Application, `cLam` +: args) =>
              assert(params.size == args.size)
              val (rargs, rctxs) = args.foldLeft((Seq.empty[Code], ctxs)) {
                case ((acc, ctxs), arg) =>
                  given Ctxs = ctxs
                  assert(CodeRes.isTerminal(arg))
                  val rarg = transform(arg, repl, ())
                  // Note: even though `arg` is a terminal, we do not necessarily have rarg.terminal == arg
                  // because `arg` could have been beta-reduced as well.
                  assert(ctxs.isPrefixOf(rarg.ctxs))
                  (acc :+ rarg.terminal, rarg.ctxs)
              }
              inlineLambda(params.zip(rargs), body)(using env, rctxs)
            case _ => super.transformImpl(c, repl, ())
          }
        }

        val inlined = inliner.transform(in, Map.empty, ())(using env, prev)
        assert(prev.isPrefixOf(inlined.ctxs))
        // Note: here, we "restart from the beginning", we discard the current `partialCr`
        val (u, c, minCr) = inlined.ctxs.plugged(prev, inlined.terminal)
        assert(prev.isPrefixOf(minCr.ctxs))
        (u, c, PartialCodeRes(minCr.terminal, minCr.ctxs.ctxs.drop(prev.ctxs.size)))
      }

      assert(u.allSuffixes(Ctxs(prev.ctxs :+ toPlug).impureParts))

      val (u2, c2, partialCr2) = toPlug match {
        case Ctx.Assumed(cond) => (u, c, Ctx.Assumed(cond) +: partialCr)

        case Ctx.BoundDef(terminal) =>
          assert(CodeRes.isTerminal(terminal))
          assert(!isLitOrVar(terminal))
          val composition = occurrencesOf(terminal)(using env, prev) // The composition comprises the terminal
          assert(composition(terminal).isOnce)
          val compWoTerm = composition - terminal
          val definitionOccurrence = u(terminal)
          val bdgCase = needsBinding(terminal, compWoTerm, u)(using env, prev)

          (bdgCase, definitionOccurrence) match {
            case (BindingCase.MustBind, _) =>
              val cLet = codeOfSig(mkLet(terminal, c), codeTpe(c))
              val u2 = compWoTerm ++ u.setTo(terminal, Occurrence.Once(prev.impureParts, env.nesting, OccurrenceKind.Expanded))
              (u2, cLet, Ctx.BoundDef(terminal) +: partialCr)
            case (BindingCase.Inlinable, Occurrence.Once(_, _, OccurrenceKind.Applied)) if isLambda(terminal) =>
              inlineAppliedLambda(terminal, c)
            case _ =>
              val (u2, partialCr2) = definitionOccurrence match {
                case Occurrence.Zero => (u, partialCr)
                case Occurrence.Once(inCtxs, nesting, _) =>
                  // In short: we use `definitionOccurrence` to update the occurrences of the terminal's components
                  val u2 = u ++ compWoTerm.withInlinedOccurrences(inCtxs.withRemovedBinding(terminal), nesting)
                  (u2, Ctx.BoundDef(terminal) +: partialCr)
                case Occurrence.Many =>
                  // This case occurs for expression satisfying `mayDuplicate`
                  (u ++ compWoTerm.manyied, Ctx.BoundDef(terminal) +: partialCr)
              }
              val u3 = u2.withRemovedBinding(terminal)
              (u3, c, partialCr2)
          }

        case Ctx.AssumeLike(lab, predTerminal) =>
          assert(CodeRes.isTerminal(predTerminal))
          assert(prev.isLitVarOrBoundDef(predTerminal))
          val u2 = u ++ occurrencesOf(predTerminal)(using env, prev)
          val c2 = codeOfSig(mkAssumeLike(lab, predTerminal, c), codeTpe(c))
          (u2, c2, Ctx.AssumeLike(lab, predTerminal) +: partialCr)
      }

      assert(u2.allSuffixes(prev.impureParts))
      (u2, c2, partialCr2)
    }
  }

  private val pluggedOccMap = mutable.Map.empty[(Env, Code), mutable.Map[Ctxs, (Occurrences, CodeRes)]]

  case class CodeRes(terminal: Code, ctxs: Ctxs) {
    assert(CodeRes.isTerminal(terminal), s"$terminal is not a terminal (but a ${code2sig(terminal)})")
    assert(ctxs.isLitVarOrBoundDef(terminal))
    assert(ctxs.terminalPartsBound(terminal))

    lazy val hc: Int = java.util.Objects.hash(terminal, ctxs)
    override def hashCode(): Int = hc

    def selfPlugged(inCtxs: Ctxs)(using env: Env): (Occurrences, Code) = {
      assert(inCtxs.isPrefixOf(ctxs))
      pluggedMap.getOrElseUpdate((this, inCtxs, env), {
        val (u2, c, minimizedCr) = ctxs.plugged(inCtxs, terminal)
        assert(codeTpe(terminal) == codeTpe(c), s"${codeTpe(terminal)} != ${codeTpe(c)}")
        // Note: we don't necessarily have minimizedCr.terminal == terminal due to lambda inlining

        locally {
          val currEntry = unplugMap.getOrElse((c, env), Map.empty)
          val newEntry = currEntry + (inCtxs -> (minimizedCr, u2))
          unplugMap += (c, env) -> newEntry
        }

        locally {
          val currEntry = pluggedOccMap.getOrElseUpdate((env, c), mutable.Map.empty)
          if (debug) {
            val u2WithoutMany = Occurrences(u2.c2u.filter(_._2.isOnce))
            val alreadyThere = currEntry.get(inCtxs)
            val got = alreadyThere.map { case (expected0, _) =>
              val expected = Occurrences(expected0.c2u.filter(_._2.isOnce))
              val eq = u2WithoutMany.c2u.toSet.intersect(expected.c2u.toSet)
              val diff = (u2WithoutMany.c2u.toSet ++ expected.c2u.toSet) -- eq
              (expected, eq, diff)
            }
            assert(got.forall(_._1 == u2WithoutMany))
          }

          currEntry += inCtxs -> (u2, minimizedCr)
        }
        (u2, c)
      })
    }

    def derived(newTerminal: Code)(using env: Env): CodeRes =
      CodeRes(newTerminal, ctxs.addBoundDef(newTerminal))
  }

  object CodeRes {
    def isTerminal(c: Code): Boolean = code2sig(c) match {
      case Signature(Label.Assume | Label.Assert | Label.Require | Label.Decreases | Label.Let, _) => false
      case _ => true
    }

    def ifExpr(cond: CodeRes, thenn: CodeRes, els: CodeRes, tpe: Type)(using env: Env): CodeRes = {
      assert(cond.ctxs.isPrefixOf(thenn.ctxs))
      assert(cond.ctxs.isPrefixOf(els.ctxs))
      val (_, cThenn) = thenn.selfPlugged(cond.ctxs.withCond(cond.terminal))
      val (_, cEls) = els.selfPlugged(cond.ctxs.withNegatedCond(cond.terminal))
      val terminal = codeOfSig(mkIfExpr(cond.terminal, cThenn, cEls), tpe)
      CodeRes(terminal, cond.ctxs.addBoundDef(terminal))
    }

    // For Lambda, Choose and Forall
    def lambdaLike(lab: Label.LambdaLike, body: CodeRes, tpe: Type)(using env: Env, ctxs: Ctxs): CodeRes = {
      assert(ctxs.isPrefixOf(body.ctxs))
      val (_, cBody) = body.selfPlugged(ctxs)(using env.incIf(lab))
      val terminal = codeOfSig(mkLambdaLike(lab, cBody), tpe)
      CodeRes(terminal, ctxs.addBoundDef(terminal))
    }

    def ensuring(body: CodeRes, pred: CodeRes, tpe: Type)(using env: Env, ctxs: Ctxs): CodeRes = {
      assert(ctxs.isPrefixOf(pred.ctxs))
      assert(ctxs.isPrefixOf(body.ctxs))
      val (_, cBody) = body.selfPlugged(ctxs)
      val (_, cPred) = pred.selfPlugged(ctxs)
      val terminal = code2sig(cPred) match {
        case Signature(Label.Lambda(_), Seq(`trueCode`)) => cBody
        case _ => codeOfSig(mkEnsuring(cBody, cPred), tpe)
      }
      CodeRes(terminal, ctxs.addBoundDef(terminal))
    }

    def matchExpr(scrut: CodeRes, cases: Seq[CodeResMatchCase], tpe: Type)(using env: Env): CodeRes = {
      assert(cases.nonEmpty)
      val terminal = codeOfSig(mkMatchExpr(scrut.terminal, cases.map(_.mc)), tpe)
      CodeRes(terminal, scrut.ctxs.addBoundDef(terminal))
    }

    def passes(scrut: CodeRes, cases: Seq[CodeResMatchCase], tpe: Type)(using env: Env): CodeRes = {
      assert(cases.nonEmpty)
      assert(codeTpe(scrut.terminal) match {
        case TupleType(bases) => bases.size == 2
        case _ => false
      })
      val terminal = codeOfSig(mkPasses(scrut.terminal, cases.map(_.mc)), tpe)
      CodeRes(terminal, scrut.ctxs.addBoundDef(terminal))
    }

    def err(ofTpe: Type, descr: String, tpe: Type)(using env: Env, ctxs: Ctxs): CodeRes = {
      val terminal = codeOfSig(mkError(ofTpe, descr), tpe)
      CodeRes(terminal, ctxs.addBoundDef(terminal))
    }

    def noTree(ofTpe: Type, tpe: Type)(using env: Env, ctxs: Ctxs): CodeRes = {
      val terminal = codeOfSig(mkNoTree(ofTpe), tpe)
      CodeRes(terminal, ctxs.addBoundDef(terminal))
    }
  }

  final def combineCodeRes(codeRess: Seq[CodeRes], tpe: Type)(cons: Seq[Code] => Signature)(using Env, Ctxs): CodeRes =
    combineCodeRes(codeRess)(cs => codeOfSig(cons(cs), tpe))

  // Badly named, but only for expressions of the form C(args) (such as: ADT, fn call, etc. but no control flow)
  final def combineCodeRes(codeRess: Seq[CodeRes])(cons: Seq[Code] => Code)(using env: Env, ctxs: Ctxs): CodeRes = {
    assert(codeRess.isEmpty || (ctxs eq codeRess.last.ctxs))
    assert(codeRess.forall(_.ctxs.isPrefixOf(ctxs)))
    assert(codeRess.size <= 1 || codeRess.zip(codeRess.tail).forall { case (prev, cur) => prev.ctxs.isPrefixOf(cur.ctxs) })

    val terminal = cons(codeRess.map(_.terminal))
    assert(!isLambdaLike(terminal))
    CodeRes(terminal, ctxs.addBoundDef(terminal))
  }

  final def unplugged(c: Code)(using env: Env, ctxs: Ctxs): Option[(CodeRes, Occurrences)] =
    unplugMap.get((c, env)).flatMap(_.get(ctxs))

  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Expr -> Code

  final def codeOfExpr(e: Expr)(using env: Env, ctxs: Ctxs, subst: LetValSubst): CodeRes = {
    val tpe = e.getType
    val res = e match {
      case v: Variable =>
        val c = subst.get(v).getOrElse(codeOfVarId(idOfVariable(v)))
        return CodeRes(c, ctxs) // This is a binding, we early return because we do not need to simplify it.

      case l: Literal[_] => CodeRes(codeOfLit(l), ctxs)

      case IfExpr(cond, thenn, els) =>
        val rcond = codeOfExpr(cond)
        val ctxsThen = rcond.ctxs.withCond(rcond.terminal)
        val rthenn = codeOfExpr(thenn)(using env, ctxsThen)
        val ctxsEls = rcond.ctxs.withNegatedCond(rcond.terminal)
        val rels = codeOfExpr(els)(using env, ctxsEls)
        CodeRes.ifExpr(rcond, rthenn, rels, tpe)

      case e: (Lambda | Choose | Forall) =>
        val (lab: Label.LambdaLike, body) = (e match {
          case Lambda(params, body) =>
            val vParams = params.map(vd => idOfVariable(vd.toVariable))
            (Label.Lambda(vParams), body)
          case Choose(res, pred) =>
            val vId = idOfVariable(res.toVariable)
            (Label.Choose(vId), pred)
          case Forall(params, pred) =>
            val vParams = params.map(vd => idOfVariable(vd.toVariable))
            (Label.Forall(vParams), pred)
        }): @unchecked
        val rbody = codeOfExpr(body)(using env.incIf(lab))
        CodeRes.lambdaLike(lab, rbody, tpe)

      case Let(vd, e, body) =>
        val re = codeOfExpr(e)
        assert(re.ctxs.isLitVarOrBoundDef(re.terminal))
        assert(!code2sig(re.terminal).label.isEnsuring)
        codeOfExpr(body)(using env, re.ctxs, subst + (vd.toVariable -> re.terminal))

      case e: (Assume | Assert | Require | Decreases) =>
        val (lab: Label.AssumeLike, pred, body) = (e match {
          case Assume(pred, body) => (Label.Assume, pred, body)
          case Assert(pred, _, body) => (Label.Assert, pred, body)
          case Require(pred, body) => (Label.Require, pred, body)
          case Decreases(measure, body) => (Label.Decreases, measure, body)
        }): @unchecked
        val rpred = codeOfExpr(pred)
        assert(rpred.ctxs.isLitVarOrBoundDef(rpred.terminal))
        codeOfExpr(body)(using env, rpred.ctxs.withAssumeLike(lab, rpred.terminal))

      case Ensuring(body, pred) =>
        val rbody = codeOfExpr(body)
        val rpred = codeOfExpr(pred) // Using the default ctxs (not rbody.ctxs)
        CodeRes.ensuring(rbody, rpred, tpe)

      case ADT(id, tps, args) => codeOfExprsBound(args, tpe)(mkADT(id, tps, _))
      case Tuple(args) => codeOfExprsBound(args, tpe)(mkTuple)
      case FunctionInvocation(id, tps, args) => codeOfExprsBound(args, tpe)(mkFunInvoc(id, tps, _))
      case Application(callee, args) => codeOfExprsBound(callee +: args, tpe) { case cCallee +: cArgs => mkApp(cCallee, cArgs) }
      case IsConstructor(e, id) =>
        val adt @ ADTType(_, _) = e.getType: @unchecked
        codeOfExprsBound(e, tpe)(mkIsCtor(_, adt, id))
      case s @ ADTSelector(e, selector) =>
        val adt @ ADTType(_, _) = e.getType: @unchecked
        codeOfExprsBound(e, tpe)(mkADTSelector(_, adt, s.constructor, selector))

      case and @ (And(_) | SplitAnd(_)) =>
        val ands = unAnd(and)
        codeOfExpr(Not(Or(ands.map(Not.apply))))
      case or @ Or(_) => transformDisjunction(unOr(or))(codeOfExpr)
      case Not(e) => negExprOf(e)
      case i @ Implies(_, _) => transformDisjunction(unOr(i))(codeOfExpr)

      case Annotated(e, flags) => codeOfExprsBound(e, tpe)(mkAnnot(_, flags))

      case Equals(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkEquals)
      case LessThan(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkLessThan)
      case GreaterThan(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkGreaterThan)
      case LessEquals(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkLessEquals)
      case GreaterEquals(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkGreaterEquals)
      case UMinus(e) => codeOfExprsBound(e, tpe)(mkUMinus)
      case Plus(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkPlus)
      case Minus(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkMinus)
      case Times(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkTimes)
      case Division(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkDivision)
      case Remainder(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkRemainder)
      case Modulo(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkModulo)
      case BVNot(e) => codeOfExprsBound(e, tpe)(mkBVNot)
      case BVAnd(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVAnd)
      case BVOr(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVOr)
      case BVXor(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVXor)
      case BVShiftLeft(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVShiftLeft)
      case BVAShiftRight(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVAShiftRight)
      case BVLShiftRight(e1, e2) => codeOfExprsBound(e1, e2, tpe)(mkBVLShiftRight)
      case BVNarrowingCast(e, newTpe) => codeOfExprsBound(e, tpe)(mkBVNarrowingCast(_, newTpe))
      case BVWideningCast(e, newTpe) => codeOfExprsBound(e, tpe)(mkBVWideningCast(_, newTpe))
      case BVUnsignedToSigned(e) => codeOfExprsBound(e, tpe)(mkBVUnsignedToSigned)
      case BVSignedToUnsigned(e) => codeOfExprsBound(e, tpe)(mkBVSignedToUnsigned)

      case TupleSelect(e, index) => codeOfExprsBound(e, tpe)(mkTupleSelect(_, index))

      case StringConcat(lhs, rhs) => codeOfExprsBound(lhs, rhs, tpe)(mkStringConcat)
      case SubString(expr, start, end) => codeOfExprsBound(expr, start, end, tpe)(mkSubString)
      case StringLength(expr) => codeOfExprsBound(expr, tpe)(mkStringLength)

      case FiniteSet(elems, base) => codeOfExprsBound(elems, tpe)(mkFiniteSet(_, base))
      case SetAdd(set, elem) => codeOfExprsBound(set, elem, tpe)(mkSetAdd)
      case ElementOfSet(elem, set) => codeOfExprsBound(elem, set, tpe)(mkElementOfSet)
      case SubsetOf(lhs, rhs) => codeOfExprsBound(lhs, rhs, tpe)(mkSubsetOf)
      case SetIntersection(lhs, rhs) => codeOfExprsBound(lhs, rhs, tpe)(mkSetIntersection)
      case SetUnion(lhs, rhs) => codeOfExprsBound(lhs, rhs, tpe)(mkSetUnion)
      case SetDifference(lhs, rhs) => codeOfExprsBound(lhs, rhs, tpe)(mkSetDifference)

      case FiniteArray(elems, base) => codeOfExprsBound(elems, tpe)(mkFiniteArray(_, base))
      case LargeArray(elems, default, size, base) =>
        if (elems.nonEmpty) throw UnsupportedOperationException("elems is not empty")
        codeOfExprsBound(default, size, tpe)(mkLargeArray(Map.empty, _, _, base))
      case ArraySelect(array, index) => codeOfExprsBound(array, index, tpe)(mkArraySelect)
      case ArrayUpdated(array, index, v) => codeOfExprsBound(array, index, v, tpe)(mkArrayUpdated)
      case ArrayLength(array) => codeOfExprsBound(array, tpe)(mkArrayLength)

      case FiniteMap(pairs, default, keyType, valueType) =>
        codeOfExprsBound(pairs.flatMap(p => Seq(p._1, p._2)) :+ default, tpe) {
          case cPairs :+ cDefault =>
            assert(cPairs.size == 2 * pairs.size)
            val cElems = cPairs.grouped(2).map { case Seq(fst, snd) => (fst, snd) }.toSeq
            mkFiniteMap(cElems, cDefault, keyType, valueType)
        }
      case MapApply(map, key) => codeOfExprsBound(map, key, tpe)(mkMapApply)
      case MapUpdated(map, key, value) => codeOfExprsBound(map, key, value, tpe)(mkMapUpdated)

      case Error(ofTpe, descr) => CodeRes.err(ofTpe, descr, tpe)
      case NoTree(ofTpe) => CodeRes.noTree(ofTpe, tpe)

      case MatchExpr(scrut, cases) =>
        // We do something similar to the case for IfExpr
        val rscrut = codeOfExpr(scrut)
        assert(codeTpe(rscrut.terminal) == scrut.getType, s"${codeTpe(rscrut.terminal)} != ${scrut.getType}")
        val rcases = signatureOfCases(rscrut.terminal, cases, Seq.empty)(using env, rscrut.ctxs)
        CodeRes.matchExpr(rscrut, rcases, tpe)

      case Passes(in, out, cases) =>
        val rin = codeOfExpr(in)
        val rout = codeOfExpr(out)(using env, rin.ctxs)
        val tupleScrutCr = {
          val tpe = TupleType(Seq(in.getType, out.getType))
          val code = codeOfSig(mkTuple(Seq(rin.terminal, rout.terminal)), tpe)
          rout.derived(code)
        }
        val rcases = signatureOfCases(tupleScrutCr.terminal, cases, Seq.empty)(using env, tupleScrutCr.ctxs)
        CodeRes.passes(tupleScrutCr, rcases, tpe)

      case e =>
        throw new UnsupportedOperationException(s"codeOfExpr: Do not know how to handle $e")
    }
    assert(ctxs.isPrefixOf(res.ctxs))
    simplifyTopLvl(ctxs, res)
  }

  def negExprOf(child: Expr)(using env: Env, ctxs: Ctxs, subst: LetValSubst): CodeRes = {
    assert(child.getType == BoolTy)

    child match {
      case Not(e) => codeOfExpr(e)
      case LessThan(lhs, rhs) => codeOfExpr(GreaterEquals(lhs, rhs))
      case GreaterEquals(lhs, rhs) => codeOfExpr(LessThan(lhs, rhs))
      case GreaterThan(lhs, rhs) => codeOfExpr(LessEquals(lhs, rhs))
      case LessEquals(lhs, rhs) => codeOfExpr(GreaterThan(lhs, rhs))
      case And(es) => codeOfExpr(Or(es.map(Not.apply)))
      case _ =>
        val rchild = codeOfExpr(child)
        val negChild = negCodeOf(rchild.terminal)
        rchild.derived(negChild)
    }
  }

  final def codeOfExprsBound(es: Seq[Expr], tpe: Type)(cons: Seq[Code] => Signature)(using Env, Ctxs, LetValSubst): CodeRes =
    codeOfExprsBound(es)(cs => codeOfSig(cons(cs), tpe))

  final def codeOfExprsBound(e1: Expr, tpe: Type)(cons: Code => Signature)(using Env, Ctxs, LetValSubst): CodeRes =
    codeOfExprsBound(Seq(e1), tpe) { case Seq(c1) => cons(c1) }

  final def codeOfExprsBound(e1: Expr, e2: Expr, tpe: Type)(cons: (Code, Code) => Signature)(using Env, Ctxs, LetValSubst): CodeRes =
    codeOfExprsBound(Seq(e1, e2), tpe) { case Seq(c1, c2) => cons(c1, c2) }

  final def codeOfExprsBound(e1: Expr, e2: Expr, e3: Expr, tpe: Type)(cons: (Code, Code, Code) => Signature)(using Env, Ctxs, LetValSubst): CodeRes =
    codeOfExprsBound(Seq(e1, e2, e3), tpe) { case Seq(c1, c2, c3) => cons(c1, c2, c3) }

  final def codeOfExprsBound(es: Seq[Expr])(cons: Seq[Code] => Code)(using env: Env, ctxs: Ctxs, subst: LetValSubst): CodeRes = {
    given x_x: Ctxs = sys.error("Carefully select ctxs")

    val (newCtxs, codeRess) = es.foldLeft((ctxs, Seq.empty[CodeRes])) {
      case ((ctxs, codeResAcc), e) =>
        val codeResE = codeOfExpr(e)(using env, ctxs)
        assert(ctxs.isPrefixOf(codeResE.ctxs))
        (codeResE.ctxs, codeResAcc :+ codeResE)
    }

    combineCodeRes(codeRess)(cons)(using env, newCtxs)
  }

  case class CodeResMatchCase(mc: LabMatchCase, composition: Occurrences)

  final def signatureOfCase(scrut: Code, mc: MatchCase)(using env: Env, ctxs0: Ctxs, subst0: LetValSubst): (CodeResMatchCase, Seq[Code]) = {
    given x_x: Ctxs = sys.error("Carefully select ctxs")
    given ô_ô: LetValSubst = sys.error("Carefully select subst")

    def convertPattern(scrut: Code, pat: Pattern, subst0: LetValSubst): (LabelledPattern, LetValSubst) = {
      val subst1 = pat.binder.map(vd => subst0 + (vd.toVariable -> scrut)).getOrElse(subst0)

      def recHelper(subScruts: Seq[Code], subps: Seq[Pattern]): (Seq[LabelledPattern], LetValSubst) = {
        assert(subScruts.size == subps.size)
        subScruts.zip(subps).foldLeft((Seq.empty[LabelledPattern], subst1)) {
          case ((acc, subst), (subScrut, subp)) =>
            val (rsub, subst2) = convertPattern(subScrut, subp, subst)
            (acc :+ rsub, subst2)
        }
      }

      pat match {
        case WildcardPattern(_) => (LabelledPattern.Wildcard, subst1)
        case LiteralPattern(_, lit) => (LabelledPattern.Lit(lit), subst1)
        case ADTPattern(_, id, tps, subps) =>
          val subScruts = adtSubScrutinees(scrut, ADTType(id, tps))
          val (rsubs, subst2) = recHelper(subScruts, subps)
          (LabelledPattern.ADT(id, tps, rsubs), subst2)
        case TuplePattern(_, subps) =>
          val tt@TupleType(_) = codeTpe(scrut): @unchecked
          val subScruts = tupleSubscrutinees(scrut, tt)
          val (rsubs, subst2) = recHelper(subScruts, subps)
          (LabelledPattern.TuplePattern(rsubs), subst2)
        case UnapplyPattern(_, recs, id, tps, subps) =>
          if (recs.nonEmpty) throw UnsupportedOperationException("recs is not empty")
          val unapp = unapplySubScrutinees(scrut, id, tps)
          val (rsubs, subst2) = recHelper(unapp.subs, subps)
          (LabelledPattern.Unapply(Seq.empty, id, tps, rsubs), subst2)
      }
    }

    val (labPat, subst1) = convertPattern(scrut, mc.pattern, subst0)
    val PatBdgsAndConds(ctxs1, _, patConds) = addPatternBindingsAndConds(ctxs0, scrut, labPat)

    val rguard: Option[CodeRes] = mc.optGuard.map(codeOfExpr(_)(using env, ctxs1, subst1))
    val (compGuard, cGuard) = rguard.map(_.selfPlugged(ctxs1)).getOrElse((Occurrences.empty, trueCode))

    val rhsCtxs = ctxs1.withCond(cGuard)
    val rrhs = codeOfExpr(mc.rhs)(using env, rhsCtxs, subst1)
    val (compRhs, rhs) = rrhs.selfPlugged(rhsCtxs)

    val labMc = LabMatchCase(labPat, cGuard, rhs)
    (CodeResMatchCase(labMc, compGuard ++ compRhs), patConds :+ cGuard)
  }

  final def signatureOfCases(cScrut: Code, mcs: Seq[MatchCase], acc: Seq[CodeResMatchCase])
                            (using env: Env, ctxs: Ctxs, subst: LetValSubst): Seq[CodeResMatchCase] = {
    if (mcs.isEmpty) acc
    else {
      val (newMatchCase, caseConds) = signatureOfCase(cScrut, mcs.head)
      val negCaseConds = negatedConjunction(caseConds)
      signatureOfCases(cScrut, mcs.tail, acc :+ newMatchCase)(using env, ctxs.withCond(negCaseConds))
    }
  }

  final def codeOfFunctionBody(fid: Identifier): CodeRes =
    fnBodyMap.getOrElseUpdate(fid, codeOfExpr(getFunction(fid).fullBody)(
      using Env(LambdaNesting(0), forceBinding = true), Ctxs.empty, LetValSubst.empty))

  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Common to OCBSL and OL

  final def implied(rhs: Code)(using env: Env, ctxs: Ctxs): Boolean = {
    if (rhs == trueCode || ctxs.allCondsSet(rhs)) true
    else if (ctxs.allConds.isEmpty) false // because rhs != trueCode
    else !env.forceBinding && impliedImpl(rhs)
  }

  def impliedImpl(rhs: Code)(using env: Env, ctxs: Ctxs): Boolean

  /////////////////////////////

  //region Related to disjunctions processing

  def doSimplifyDisjunction(disjs: Seq[Code], polarity: Boolean)(using Env, Ctxs): Seq[Code]

  final def simplifiedDisjunction(disj0: Seq[Code], polarity: Boolean)(using env: Env, ctxs: Ctxs): Code = {
    def hasTrailingTrue(c: Code): Boolean = code2sig(c) match {
      case BoolLitSig(true) => true
      case OrSig(disjs, true) => hasTrailingTrue(disjs.last)
      case Signature(Label.Let, Seq(_, b)) => hasTrailingTrue(b)
      case Signature(_: Label.AssumeLike, Seq(_, b)) => hasTrailingTrue(b)
      case _ => false
    }

    assert(disj0.forall(c => codeTpe(c) == BoolTy))
    val disjs1 = unOrCodes(disj0).filter(_ != falseCode).distinct
    val disjs2 = doSimplifyDisjunction(disjs1, polarity)
    val simp = {
      if (disjs2.isEmpty) falseCode
      else if (disjs2.size == 1) disjs2.head
      else if (env.forceBinding) codeOfDisjs(disjs2)
      else {
        val contradictionIx = Some(disjs2.indexOf(trueCode)).filter(_ >= 0)
          .orElse(checkForDisjunctionContradiction(disjs2))
        contradictionIx match {
          case None =>
            // Nothing simplified, so just make the disjunction and return
            codeOfDisjs(disjs2)
          case Some(ix) =>
            // Due to short-circuiting, once the disjunction evaluates to true, the remaining disjuncts won't ever be evaluated
            // so it is safe to drop them -- including impure expressions.
            val disjs3 = disjs2.take(ix + 1)
            val disjs3AllPure = disjs3.forall(codePurity(_).isPure)
            if (disjs3AllPure) trueCode
            else {
              // Add a trailing `true` if not already present (because the disjunction will evaluate to true,
              // but due to the presence of impure expressions, we are not allowed to simplify the whole expr to true)
              val disjs4 = if (hasTrailingTrue(disjs3.last)) disjs3 else disjs3 :+ trueCode
              codeOfDisjs(disjs4)
            }
        }
      }
    }
    val allBoundDisjs = ctxs.bound.reverse.collect(c => code2sig(c) match {
      case OrSig(children, _) => children -> codeOfDisjs(children)
    }).toMap
    val unflattenedSimp = allBoundDisjs.foldLeft(simp) {
      case (simp, (subseq, disj)) => tryUnflatten(simp, subseq, disj)
    }

    if (polarity) unflattenedSimp else negCodeOf(unflattenedSimp)
  }

  // If in `c` we find a subsequence `subseq`, replace `subseq` with `disj` and return the result code
  // Otherwise, return `c`.
  final def tryUnflatten(c: Code, subseq: Seq[Code], replacement: Code): Code = {
    def tryReplace(disjs: Seq[Code]): Seq[Code] = {
      val subseqStart = disjs.indexOfSlice(subseq)
      if (subseqStart < 0) disjs
      else disjs.take(subseqStart) ++ Seq(replacement) ++ disjs.drop(subseqStart + subseq.length)
    }

    code2sig(c) match {
      case OrSig(cDisjs0, polarity) =>
        // Subsequence replacement in cDisjs0
        val cDisjs1 = tryReplace(cDisjs0)
        // Subsequence replacement in Not(Or(...)) nodes of cDisjs1
        val cDisjs2 = cDisjs1.foldLeft(Seq.empty[Code]) {
          case (acc, c) =>
            code2sig(c) match {
              case OrSig(_, false) =>
                val rec = tryUnflatten(c, subseq, replacement)
                acc :+ rec
              case _ => acc :+ c
            }
        }
        val updOr = codeOfDisjs(cDisjs2)
        if (polarity) updOr else negCodeOf(updOr)
      case _ => c
    }
  }

  // Return (if existing) the index k s.t.:
  //   -With polarity = true:   \/_j<=k disjs(j) === true
  //   -With polarity = false: ¬\/_j<=k disjs(j) === false
  def checkForDisjunctionContradiction(disjs: Seq[Code])(using Env, Ctxs): Option[Int]

  final def transformDisjunction[T](disjs: Seq[T])(f: Ctxs ?=> T => CodeRes)(using env: Env, outerCtxs: Ctxs): CodeRes = {
    given x_x: Ctxs = sys.error("Carefully select ctxs")

    assert(disjs.size >= 2)

    def peelDisjs(disjs: Seq[Code], ctxs: Ctxs): (Seq[CodeRes], Ctxs) = {
      disjs.foldLeft((Seq.empty[CodeRes], ctxs)) {
        case ((acc, ctxs), disj) =>
          given Ctxs = ctxs
          assert(!label(disj).isOr)
          val teared = tearDown(disj)
          (acc :+ teared, teared.ctxs.withNegatedCond(teared.terminal))
      }
    }

    def transformRec(disjs: Seq[T], rdisjsAcc: Seq[CodeRes])(using ctxs: Ctxs): Seq[CodeRes] = {
      assert(rdisjsAcc.isEmpty || rdisjsAcc.last.ctxs.isPrefixOf(ctxs))
      assert(outerCtxs.isPrefixOf(ctxs))
      if (disjs.isEmpty) rdisjsAcc
      else {
        val re: CodeRes = f(disjs.head)
        assert(codeTpe(re.terminal) == BoolTy, s"Got ${codeTpe(re.terminal)}")
        assert(ctxs.isPrefixOf(re.ctxs))
        val neg = negCodeOf(re.terminal)
        if (neg == falseCode) rdisjsAcc :+ re
        else {
          (code2sig(re.terminal), re.ctxs.pop) match {
            case (Signature(Label.Or, reDisjs), Some((rePrevCtxs, Ctx.BoundDef(lastBound)))) if re.terminal == lastBound && re.ctxs.size > ctxs.size =>
              // rePrevCtxs = re.ctxs but without this disjunction being bound
              assert(!ctxs.isBoundDef(lastBound))
              val (reDisjsCrs, nextCtxs) = peelDisjs(reDisjs, rePrevCtxs)
              transformRec(disjs.tail, rdisjsAcc ++ reDisjsCrs)(using nextCtxs)

            case _ =>
              val nextCtxs = re.ctxs.withCond(neg)
              transformRec(disjs.tail, rdisjsAcc :+ re)(using nextCtxs)
          }
        }
      }
    }

    def combineRec(disjs: Seq[CodeRes], acc: CodeRes): CodeRes = {
      disjs match {
        case Seq() => acc
        case init :+ last =>
          assert(last.ctxs.isPrefixOf(acc.ctxs))
          assert(init.forall(_.ctxs.isPrefixOf(last.ctxs)))
          assert(init.forall(i => outerCtxs.isPrefixOf(i.ctxs)))

          if (last.terminal == falseCode) {
            // We skip this one (we do not drop its ctxs because it is a prefix of acc by transformRec structure)
            combineRec(init, acc)
          } else {
            val (pluggedOcc, accPlugged) = acc.selfPlugged(last.ctxs.withNegatedCond(last.terminal))
            val preLastCtxs = init.lastOption.map(_.ctxs).getOrElse(outerCtxs)
            val mayPopLastTerminal = !preLastCtxs.isBoundDef(last.terminal)
            val newAcc = simplifiedDisjunctionCodeRes(last, accPlugged, pluggedOcc, mayPopLastTerminal, polarity = true)
            combineRec(init, newAcc)
          }
      }
    }

    val disjsCodeRes = transformRec(disjs, Seq.empty)(using outerCtxs)
    val last = disjsCodeRes.last
    val initAcc = CodeRes(falseCode, last.ctxs.withNegatedCond(last.terminal))
    combineRec(disjsCodeRes, initAcc)
  }

  def simplifiedDisjunctionCodeRes(lhs: CodeRes, rhs: Code, mayPopCtxs: Boolean, polarity: Boolean)(using env: Env): CodeRes = {
    val rhsComp = occurrencesOf(rhs)(using env, lhs.ctxs)
    simplifiedDisjunctionCodeRes(lhs, rhs, rhsComp, mayPopCtxs, polarity)
  }

  def simplifiedDisjunctionCodeRes(lhs: CodeRes, rhs: Code, rhsComp: Occurrences, mayPopCtxs: Boolean, polarity: Boolean)(using env: Env): CodeRes = {
    val newDisjs = simplifiedDisjunction(Seq(lhs.terminal, rhs), polarity)(using env, lhs.ctxs)
    // TODO: Explanation
    val prevCtxs = {
      // TODO: This condition on rhsComp to avoid some duplication like in System-F is not perfect because disjunctions are always flattened
      if (mayPopCtxs && label(lhs.terminal).isOr && rhsComp(lhs.terminal).isZero) {
        lhs.ctxs.pop match {
          case Some((prevCtxs, Ctx.BoundDef(lastBdg))) if lastBdg == lhs.terminal => prevCtxs
          case _ => lhs.ctxs
        }
      } else {
        lhs.ctxs
      }
    }
    tearDown(newDisjs)(using env, prevCtxs)
  }

  //endregion

  /////////////////////////////


  // TODO: May result in some duplication no?
  final def negCodeOf(c: Code): Code = {
    assert(codeTpe(c) == BoolTy, s"Got ${codeTpe(c)}")
    negCodeCache.get(c) match {
      case Some(n) => return n
      case None => ()
    }

    val res = code2sig(c) match {
      case Signature(Label.Not, Seq(cc)) => cc
      case BoolLitSig(b) => b2c(!b)
      case LtSig(lhs, rhs) => codeOfSig(mkGreaterEquals(lhs, rhs), BoolTy)
      case GeqSig(lhs, rhs) => codeOfSig(mkLessThan(lhs, rhs), BoolTy)
      case GtSig(lhs, rhs) => codeOfSig(mkLessEquals(lhs, rhs), BoolTy)
      case LeqSig(lhs, rhs) => codeOfSig(mkGreaterThan(lhs, rhs), BoolTy)

      case Signature(Label.IfExpr, Seq(cond, thenn, els)) =>
        codeOfSig(mkIfExpr(cond, negCodeOf(thenn), negCodeOf(els)), BoolTy)

      case Signature(Label.Let, Seq(e, body)) =>
        codeOfSig(mkLet(e, negCodeOf(body)), BoolTy)

      case Signature(lab: Label.AssumeLike, Seq(pred, body)) =>
        codeOfSig(mkAssumeLike(lab, pred, negCodeOf(body)), BoolTy)

      case MatchExprSig(scrut, cases) =>
        val ncases = cases.map(c => c.copy(rhs = negCodeOf(c.rhs)))
        codeOfSig(mkMatchExpr(scrut, ncases), BoolTy)

      case _ =>
        assert(CodeRes.isTerminal(c))
        codeOfSig(mkNot(c), BoolTy)
    }

    negCodeCache += c -> res
    negCodeCache += res -> c

    res
  }

  final def conjunct(conj: Seq[Code])(using Env, Ctxs): Code = simplifiedDisjunction(conj.map(negCodeOf), polarity = false)

  final def negatedConjunction(conj: Seq[Code])(using Env, Ctxs): Code = simplifiedDisjunction(conj.map(negCodeOf), polarity = true)

  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Code general simplification

  final def simplifyTopLvl(pre: Ctxs, cr: CodeRes)(using env: Env): CodeRes = {
    val tpe = codeTpe(cr.terminal)
    lazy val zero = codeOfIntLit(0, tpe)
    lazy val one = codeOfIntLit(1, tpe)

    val simp = code2sig(cr.terminal) match {
      case Signature(Label.IfExpr, Seq(cond, thenn, els)) =>
        assert(CodeRes.isTerminal(cond))
        assert(cr.ctxs.isLitVarOrBoundDef(cond))

        // 1. If cr.ctxs contains this code as a last BoundDef, it implies we are going to simplify the "definition"
        // (in an equivalent let v = e, we are going to simplify `e`).
        // 2. Otherwise, then cr.terminal is a bound occurrence by a previous BoundDef.
        // In case 1, we use the ctxs without the last BoundDef
        // In case 2, we use cr.ctxs
        val (prevCtxs, condCtxs) = cr.ctxs.ctxs match {
          case prevCtxs :+ (bCond@Ctx.BoundDef(cond2)) :+ Ctx.BoundDef(ifExpr2) if cond2 == cond && cr.terminal == ifExpr2 =>
            (Ctxs(prevCtxs), Ctxs(prevCtxs :+ bCond))

          case prevCtxs :+ Ctx.BoundDef(ifExpr2) if cr.terminal == ifExpr2 =>
            val prevCtxss = Ctxs(prevCtxs)
            assert(prevCtxss.isLitVarOrBoundDef(cond))
            (prevCtxss, prevCtxss)

          case _ =>
            assert(cr.ctxs.isLitVarOrBoundDef(cond))
            (cr.ctxs, cr.ctxs)
        }
        val condCr = CodeRes(cond, condCtxs)
        val ctxsForThen = condCtxs.withCond(cond)
        val ctxsForEls = condCtxs.withNegatedCond(cond)
        lazy val negCond = negCodeOf(cond)

        val fstTry: Option[CodeRes] = {
          def unplugBranch(branch: Code, branchCtx: Ctxs): CodeRes = {
            val Some((branchCr0, _)) = unplugged(branch)(using env, branchCtx): @unchecked
            assert(branchCtx.isPrefixOf(branchCr0.ctxs))
            // resCtxs is like branchCr0.ctx but without the Assumed(cond) (or Assumed(neg(cond))) coming from branchCtx
            val resCtxs = condCtxs.addExtraWithoutAssumed(branchCr0.ctxs)
            CodeRes(branchCr0.terminal, resCtxs)
          }

          // Note: purity check is unneeded because:
          //  -For cond: due to being bound
          //  -For "dead" branch: because unreachable anyway
          if (cond == trueCode || thenn == els || implied(cond)(using env, condCtxs)) {
            Some(unplugBranch(thenn, ctxsForThen))
          } else if (cond == falseCode || implied(negCond)(using env, condCtxs)) {
            Some(unplugBranch(els, ctxsForEls))
          } else None
        }

        def sndTry: CodeRes = {
          lazy val mayPopCond = !prevCtxs.isBoundDef(cond)
          lazy val mayPopNegCond = !prevCtxs.isBoundDef(negCond)

          (code2sig(thenn), code2sig(els)) match {
            case (BoolLitSig(true), BoolLitSig(false)) => CodeRes(cond, condCtxs)

            case (BoolLitSig(false), BoolLitSig(true)) =>
              CodeRes(negCond, condCtxs.addBoundDef(negCond))

            case (BoolLitSig(true), _) =>
              simplifiedDisjunctionCodeRes(condCr, els, mayPopCond, polarity = true)

            case (_, BoolLitSig(true)) =>
              simplifiedDisjunctionCodeRes(condCr.derived(negCond), thenn, mayPopNegCond, polarity = true)

            case (BoolLitSig(false), _) =>
              // -> !cond && els === !(cond || !els)
              simplifiedDisjunctionCodeRes(condCr, negCodeOf(els), mayPopCond, polarity = false)

            case (_, BoolLitSig(false)) =>
              // -> cond && then === !(!cond || !thenn)
              simplifiedDisjunctionCodeRes(condCr.derived(negCond), negCodeOf(thenn), mayPopNegCond, polarity = false)

            case (Signature(Label.IfExpr, Seq(cond2, thenn2, `els`)), _) =>
              // -> if (cond && cond2) thenn2 else els === if (!(!cond || !cond2)) thenn2 else els
              val negCond2 = negCodeOf(cond2)
              val combinedCond = simplifiedDisjunctionCodeRes(condCr.derived(negCond), negCond2, mayPopNegCond, polarity = false)
              val newIfCode = codeOfSig(mkIfExpr(combinedCond.terminal, thenn2, els), tpe)
              combinedCond.derived(newIfCode)

            case (_, Signature(Label.IfExpr, Seq(cond2, `thenn`, els2))) =>
              // -> if (cond || cond2) thenn else els2
              val combinedCond = simplifiedDisjunctionCodeRes(condCr, cond2, mayPopCond, polarity = true)
              val newIfCode = codeOfSig(mkIfExpr(combinedCond.terminal, thenn, els2), tpe)
              combinedCond.derived(newIfCode)

            case _ => cr
          }
        }
        fstTry.getOrElse(sndTry)

      case Signature(Label.IsConstructor(adt, id), Seq(e)) =>
        isConstructor(e, adt, id)(using env, cr.ctxs) match {
          case Some(b) => cr.derived(b2c(b))
          case None => cr
        }

      case Signature(lab@Label.ADTSelector(_, _, _), Seq(e)) =>
        cr.derived(adtSelect(e, lab, tpe))

      case Signature(Label.FunctionInvocation(fn, Seq()), Seq()) if codePurityInst.fnPurity(fn).isPure =>
        codeOfExpr(getFunction(fn).fullBody)(using env, cr.ctxs, LetValSubst.empty)

      case Signature(Label.ADT(id, tps), args) =>
        // Simplification of ADT(base.fld1, base.fld2, etc.) in base if base is the same as the ADT of this expression.
        val ctor: TypedADTConstructor = getConstructor(id, tps)
        assert(ctor.fields.size == args.size)

        def sameBase(i: Int, baseSoFar: Option[Code]): Option[Code] = {
          if (i == args.size) baseSoFar
          else {
            val fldId: Identifier = ctor.fields(i).id
            code2sig(args(i)) match {
              // TODO: SimplifierWithPC checks for e.getType == adt.getType, but we do ctor == ctor2, is it alright as well?
              case Signature(Label.ADTSelector(_, ctor2, sel), Seq(base))
                if fldId == sel && ctor == ctor2 &&
                  baseSoFar.forall(_ == base) &&
                  isConstructor(base, ADTType(id, tps), id)(using env, cr.ctxs) == Some(true) =>
                sameBase(i + 1, Some(base))
              case _ => None // The adventure ends here, sadly
            }
          }
        }

        sameBase(0, None) match {
          case Some(base) => cr.derived(base)
          case None => cr
        }

      case Signature(Label.TupleSelect(i), Seq(e)) =>
        cr.derived(tupleSelect(e, i, tpe))

      case Signature(Label.ArraySelect, Seq(arr, i)) =>
        def getVal(arr: Code): Option[Code] = code2sig(arr) match {
          case Signature(Label.ArrayUpdated, Seq(arr2, j, newValue)) =>
            if (i == j) Some(newValue)
            else {
              // If `i` and `j` are provably different, we can recur on `arr2`
              // Otherwise, we cannot be sure if we need to return `newValue`, or the result of the recursion
              val ijNeq = (label(i), label(j)) match {
                case (li@Label.Lit(_), lj@Label.Lit(_)) => li != lj
                case _ =>
                  Seq(codeOfSig(mkEquals(i, j), BoolTy), codeOfSig(mkEquals(j, i), BoolTy))
                    .map(c => codeOfSig(mkNot(c), BoolTy))
                    .exists(cr.ctxs.allCondsSet.contains)
              }
              if (ijNeq) getVal(arr2)
              else None
            }
          case Signature(Label.LargeArray(_, _), elems :+ default :+ _) if elems.isEmpty =>
            Some(default)
          case Signature(Label.FiniteArray(_), elems) =>
            code2sig(i) match {
              case Signature(Label.Lit(Int32Literal(ii)), _) => Some(elems(ii))
              case _ => None
            }
          case _ => None
        }
        getVal(arr).map(cr.derived)
          .getOrElse(cr)

      case Signature(Label.ArrayLength, Seq(arr)) =>
        def getLen(currArr: Code): CodeRes = code2sig(currArr) match {
          case Signature(Label.ArrayUpdated, Seq(newArr, _, _)) => getLen(newArr)
          case Signature(Label.FiniteArray(_), elems) =>
            cr.derived(codeOfLit(Int32Literal(elems.size)))
          case Signature(Label.LargeArray(_, _), _ :+ _ :+ size) =>
            cr.derived(size)
          case _ =>
            if (currArr == arr) cr
            else cr.derived(codeOfSig(mkArrayLength(currArr), tpe))
        }
        getLen(arr)

      case Signature(Label.Not, Seq(e)) =>
        code2sig(e) match {
          case Signature(Label.Not, Seq(e2)) => cr.derived(e2)
          case _ => cr
        }

      case Signature(lab@(Label.Equals | Label.GreaterEquals | Label.LessEquals | Label.LessThan | Label.GreaterThan), Seq(e1, e2)) =>
        generateCond(pre, cr, lab, e1, e2)

      case Signature(Label.UMinus, Seq(e)) =>
        code2sig(e) match {
          case Signature(Label.UMinus, Seq(e2)) => cr.derived(e2)
          case _ => cr
        }

      case Signature(lab@(Label.Plus | Label.Times), Seq(e1, e2)) =>
        cr.derived(flattenAssocArith(lab, e1, e2))

      case MinusSig(e1, e2) =>
        def minus(lit: BigInt, a: Code): CodeRes = {
          val res =
            if (lit == 0) codeOfSig(mkUMinus(a), tpe)
            else codeOfSig(mkMinus(codeOfIntLit(lit, tpe), a), tpe)
          cr.derived(res)
        }
        def plus(a: Code, lit: BigInt): CodeRes = {
          val res =
            if (lit == 0) a
            else if (lit < 0) codeOfSig(mkMinus(a, codeOfIntLit(-lit, tpe)), tpe)
            else codeOfSig(mkPlus(a, codeOfIntLit(lit, tpe)), tpe)
          cr.derived(res)
        }

        assert(codeTpe(e1) == tpe && codeTpe(e1) == codeTpe(e2))
        if (e1 == e2) cr.derived(zero)
        else (code2sig(e1), code2sig(e2)) match {
          case (IntLikeLitSig(i1), IntLikeLitSig(i2)) =>
            cr.derived(codeOfIntLit(i1 - i2, tpe))

          case (MinusSig(a, IntLikeLitCode(i1)), IntLikeLitSig(i2)) =>
            plus(a, -(i1 + i2))

          case (MinusSig(IntLikeLitCode(i1), a), IntLikeLitSig(i2)) =>
            minus(i1 - i2, a)

          case (PlusSig(a, IntLikeLitCode(i1)), IntLikeLitSig(i2)) =>
            plus(a, i1 - i2)

          case (PlusSig(IntLikeLitCode(i1), a), IntLikeLitSig(i2)) =>
            plus(a, i1 - i2)

          case (PlusSig(IntLikeLitCode(i1), a), PlusSig(IntLikeLitCode(i2), b)) =>
            plus(codeOfSig(mkMinus(a, b), tpe), i1 - i2)

          case (PlusSig(a, IntLikeLitCode(i1)), PlusSig(IntLikeLitCode(i2), b)) =>
            plus(codeOfSig(mkMinus(a, b), tpe), i1 - i2)

          case (PlusSig(IntLikeLitCode(i1), a), PlusSig(b, IntLikeLitCode(i2))) =>
            plus(codeOfSig(mkMinus(a, b), tpe), i1 - i2)

          case (PlusSig(a, IntLikeLitCode(i1)), PlusSig(b, IntLikeLitCode(i2))) =>
            plus(codeOfSig(mkMinus(a, b), tpe), i1 - i2)

          case _ => cr
        }

      case Signature(lab@(Label.Division | Label.Remainder | Label.Modulo), Seq(e1, e2)) =>
        val resIfEq = lab match {
          case Label.Division => one
          case Label.Remainder | Label.Modulo => zero
        }
        if (opts.assumeChecked && e2 != zero && e1 == zero) cr.derived(zero)
        else if (opts.assumeChecked && e2 != zero && e1 == e2) cr.derived(resIfEq)
        else (code2sig(e1), code2sig(e2)) match {
          case (IntLikeLitSig(i1), IntLikeLitSig(i2)) if i2 != 0 =>
            val res = lab match {
              case Label.Division => i1 / i2
              case Label.Remainder => i1 % i2
              case Label.Modulo => if (i2 < 0) i1 mod (-i2) else i1 mod i2
            }
            cr.derived(codeOfIntLit(res, codeTpe(e1)))
          case _ => cr
        }

      case Signature(Label.BVNot, Seq(e)) =>
        code2sig(e) match {
          case Signature(Label.BVNot, Seq(e2)) => cr.derived(e2)
          case _ => cr
        }

      case Signature(Label.BVAnd, Seq(e1, e2)) =>
        if (e1 == e2) cr.derived(e1)
        else if (e1 == zero || e2 == zero) cr.derived(zero)
        else cr

      case Signature(Label.BVOr, Seq(e1, e2)) =>
        if (e1 == e2) cr.derived(e1)
        else if (e1 == zero) cr.derived(e2)
        else if (e2 == zero) cr.derived(e1)
        else cr

      case Signature(Label.BVXor, Seq(e1, e2)) =>
        if (e1 == e2) cr.derived(zero)
        else if (e1 == zero) cr.derived(e2)
        else if (e2 == zero) cr.derived(e1)
        else cr

      case Signature(Label.BVShiftLeft | Label.BVAShiftRight | Label.BVLShiftRight, Seq(e1, e2)) =>
        if (e2 == zero) cr.derived(e1) else cr

      case Signature(Label.BVWideningCast(bvt), Seq(e)) =>
        label(e) match {
          case Label.Lit(bv@BVLiteral(signed, _, _)) =>
            cr.derived(codeOfLit(BVLiteral(signed, bv.toBigInt, bvt.size)))
          case _ => cr
        }

      case Signature(Label.BVNarrowingCast(bvt), Seq(e)) =>
        label(e) match {
          case Label.Lit(bv@BVLiteral(signed, _, _)) if fits(bv.toBigInt, bvt) =>
            cr.derived(codeOfLit(BVLiteral(signed, bv.toBigInt, bvt.size)))
          case _ => cr
        }

      case MatchExprSig(scrut, cases) =>
        // See explanation for IfExpr
        val scrutCr = cr.ctxs.ctxs match {
          case prevCtxs :+ (bScrut@Ctx.BoundDef(scrut2)) :+ Ctx.BoundDef(match2) if scrut2 == scrut && cr.terminal == match2 =>
            CodeRes(scrut, Ctxs(prevCtxs :+ bScrut))

          case prevCtxs :+ Ctx.BoundDef(match2) if cr.terminal == match2 =>
            val prevCtxss = Ctxs(prevCtxs)
            assert(prevCtxss.isLitVarOrBoundDef(scrut))
            CodeRes(scrut, prevCtxss)

          case _ =>
            assert(cr.ctxs.isLitVarOrBoundDef(scrut))
            CodeRes(scrut, cr.ctxs)
        }
        simplifyCases(scrut, cases)(using env, scrutCr.ctxs) match {
          case SimplifiedCases.Empty => sys.error("ah bah là, je sais pas quoi faire...")
          case SimplifiedCases.ElidableMatchExpr(rhs) => rhs
          case SimplifiedCases.Cases(newCases) =>
            CodeRes.matchExpr(scrutCr, newCases, tpe)
        }

      case Signature(Label.Forall(_), Seq(body)) if body == trueCode || body == falseCode =>
        cr.derived(body)

      case _ => cr
    }

    if (tpe == BoolTy) {
      given Ctxs = cr.ctxs
      if (implied(cr.terminal)) simp.derived(trueCode)
      else if (implied(negCodeOf(simp.terminal))) simp.derived(falseCode)
      else simp
    }
    else simp
  }

  final def generateCond(pre: Ctxs, cr: CodeRes, rel: Label.Rel, lhs: Code, rhs: Code)(using env: Env): CodeRes = {
    assert(pre.isPrefixOf(cr.ctxs))
    assert(cr.terminal == codeOfSig(Signature(rel, Seq(lhs, rhs)), BoolTy))
    val resIfEq = rel match {
      case Label.Equals | Label.GreaterEquals | Label.LessEquals => trueCode
      case Label.LessThan | Label.GreaterThan => falseCode
    }

    def addDefinitions(ctxs: Ctxs, c: Code): Ctxs = {
      def rec(c: Code): Seq[Code] = {
        if (ctxs.isLitVarOrBoundDef(c)) return Seq.empty
        code2sig(c) match {
          case Signature(Label.IfExpr, Seq(cond, _, _)) => rec(cond) ++ Seq(cond, c)
          case Signature(Label.MatchExpr(_), scrut +: _) => rec(scrut) ++ Seq(scrut, c)
          case Signature(Label.Passes(_), scrut +: _) => rec(scrut) ++ Seq(scrut, c)
          case Signature(Label.Or, fst +: _) => rec(fst) ++ Seq(fst, c)
          case Signature(Label.Not, Seq(e)) => rec(e) ++ Seq(c)
          case Signature(_: (Label.Ensuring.type | Label.LambdaLike), _) => Seq.empty
          case Signature(_, args) => args.flatMap(a => rec(a) ++ Seq(a)) ++ Seq(c)
        }
      }

      val defs = rec(c)
      ctxs.addBoundDefs(defs)
    }

    def explodeIf(ctxs: Ctxs, cond: Code, thn: Code, els: Code): (CodeRes, Ctxs, CodeRes, Ctxs) = {
      val branchCtx = ctxs.addBoundDef(cond)
      val thenCr = tearDown(thn)(using env, branchCtx.withCond(cond))
      assert(branchCtx.isPrefixOf(thenCr.ctxs))
      val elsCr = tearDown(els)(using env, branchCtx.withNegatedCond(cond))
      assert(branchCtx.isPrefixOf(elsCr.ctxs))
      val thnSuffix = Ctxs(thenCr.ctxs.ctxs.drop(branchCtx.size))
      val elsSuffix = Ctxs(elsCr.ctxs.ctxs.drop(branchCtx.size))
      (thenCr, thnSuffix, elsCr, elsSuffix)
    }

    def resultOfIf(cond: Code, thnPlugged: Code, elsPlugged: Code, resCtxs: Ctxs): CodeRes = {
      val res = (thnPlugged, elsPlugged) match {
        case (`trueCode`, _) => simplifiedDisjunction(Seq(cond, elsPlugged), true)(using env, resCtxs)
        case (`falseCode`, _) => conjunct(Seq(negCodeOf(cond), elsPlugged))(using env, resCtxs)
        case (_, `trueCode`) => simplifiedDisjunction(Seq(negCodeOf(cond), thnPlugged), true)(using env, resCtxs)
        case (_, `falseCode`) => conjunct(Seq(cond, thnPlugged))(using env, resCtxs)
        case _ => codeOfSig(mkIfExpr(cond, thnPlugged, elsPlugged), BoolTy)
      }
      CodeRes(res, addDefinitions(resCtxs, res))
    }

    def rec(pre: Ctxs, lhsCtxs: Ctxs, lhs: Code, rhsCtxs: Ctxs, rhs: Code, resCtxs0: Ctxs, reduceComplex0: Boolean): CodeRes = {
      assert(pre.isPrefixOf(resCtxs0))
      val relCode = codeOfSig(Signature(rel, Seq(lhs, rhs)), BoolTy)
      val (resCtxs, popped) = resCtxs0.withRemovedBindingIfNoOccurrence(pre, Seq(relCode, rhs, lhs))
      assert(pre.isPrefixOf(resCtxs))
      val reduceComplex = reduceComplex0 && popped

      if (rhs == lhs) return CodeRes(resIfEq, resCtxs.addBoundDef(lhs))

      (code2sig(lhs), code2sig(rhs)) match {
        case (BoolLitSig(b), _) if rel == Label.Equals =>
          val r = if (b) rhs else negCodeOf(rhs)
          CodeRes(r, resCtxs.addBoundDef(lhs).addBoundDef(rhs).addBoundDef(r))
        case (_, BoolLitSig(b)) if rel == Label.Equals =>
          val r = if (b) lhs else negCodeOf(lhs)
          CodeRes(r, resCtxs.addBoundDef(lhs).addBoundDef(rhs).addBoundDef(r))
        case (Signature(Label.IfExpr, Seq(lhsCond, lhsThn, lhsEls)), Signature(Label.IfExpr, Seq(rhsCond, rhsThn, rhsEls))) if reduceComplex && lhsCond == rhsCond =>
          val (lhsThenCr, lhsThnSuffix, lhsElsCr, lhsElsSuffix) = explodeIf(lhsCtxs, lhsCond, lhsThn, lhsEls)
          val (rhsThenCr, rhsThnSuffix, rhsElsCr, rhsElsSuffix) = explodeIf(rhsCtxs, rhsCond, rhsThn, rhsEls)

          val thnCtxs = resCtxs.addCtxs(lhsThnSuffix).addCtxs(rhsThnSuffix)
          assert(thnCtxs.allCondsSet.contains(lhsCond))
          val thnRes = rec(resCtxs, lhsThenCr.ctxs, lhsThenCr.terminal, rhsThenCr.ctxs, rhsThenCr.terminal, thnCtxs, true)
          val (_, thnPlugged) = thnRes.selfPlugged(resCtxs.withCond(lhsCond))

          val elsCtxs = resCtxs.addCtxs(lhsElsSuffix).addCtxs(rhsElsSuffix)
          assert(elsCtxs.allCondsSet.contains(negCodeOf(lhsCond)))
          val elsRes = rec(resCtxs, lhsElsCr.ctxs, lhsElsCr.terminal, rhsElsCr.ctxs, rhsElsCr.terminal, elsCtxs, true)
          val (_, elsPlugged) = elsRes.selfPlugged(resCtxs.withNegatedCond(lhsCond))

          resultOfIf(lhsCond, thnPlugged, elsPlugged, resCtxs)

        case (Signature(Label.ADT(id1, tps1), args1), Signature(Label.ADT(id2, tps2), args2)) if rel == Label.Equals && id1 == id2 && tps1 == tps2 && args1.size == args2.size =>
          assert(args1.forall(lhsCtxs.isLitVarOrBoundDef))
          assert(args1.forall(resCtxs.isLitVarOrBoundDef))
          assert(args2.forall(rhsCtxs.isLitVarOrBoundDef))
          assert(args2.forall(resCtxs.isLitVarOrBoundDef))
          val res = transformDisjunction(args1.zip(args2)) { case (a1, a2) =>
            val res = rec(resCtxs, lhsCtxs, a1, rhsCtxs, a2, summon[Ctxs], reduceComplex)
            res.derived(negCodeOf(res.terminal))
          }(using env, resCtxs)
          res.derived(negCodeOf(res.terminal))

        case (_, Signature(Label.IfExpr, Seq(rhsCond, rhsThn, rhsEls))) if reduceComplex && !label(lhs).isIfExpr =>
          val (rhsThenCr, rhsThnSuffix, rhsElsCr, rhsElsSuffix) = explodeIf(rhsCtxs, rhsCond, rhsThn, rhsEls)
          val resCtxs2 = resCtxs.addBoundDef(lhs)
          val thnCtxs = resCtxs2.addCtxs(rhsThnSuffix)
          assert(thnCtxs.allCondsSet.contains(rhsCond))
          val thnRes = rec(resCtxs2, lhsCtxs, lhs, rhsThenCr.ctxs, rhsThenCr.terminal, thnCtxs, true)
          val (_, thnPlugged) = thnRes.selfPlugged(resCtxs2.withCond(rhsCond))

          val elsCtxs = resCtxs2.addCtxs(rhsElsSuffix)
          assert(elsCtxs.allCondsSet.contains(negCodeOf(rhsCond)))
          val elsRes = rec(resCtxs2, lhsCtxs, lhs, rhsElsCr.ctxs, rhsElsCr.terminal, elsCtxs, true)
          val (_, elsPlugged) = elsRes.selfPlugged(resCtxs2.withNegatedCond(rhsCond))

          resultOfIf(rhsCond, thnPlugged, elsPlugged, resCtxs2)

        case (Signature(Label.IfExpr, Seq(lhsCond, lhsThn, lhsEls)), _) if reduceComplex && !label(rhs).isIfExpr =>
          val (lhsThenCr, lhsThnSuffix, lhsElsCr, lhsElsSuffix) = explodeIf(lhsCtxs, lhsCond, lhsThn, lhsEls)

          val resCtxs2 = resCtxs.addBoundDef(rhs)
          val thnCtxs = resCtxs2.addCtxs(lhsThnSuffix)
          assert(thnCtxs.allCondsSet.contains(lhsCond))
          val thnRes = rec(resCtxs, lhsThenCr.ctxs, lhsThenCr.terminal, rhsCtxs, rhs, thnCtxs, true)
          val (_, thnPlugged) = thnRes.selfPlugged(resCtxs2.withCond(lhsCond))

          val elsCtxs = resCtxs2.addCtxs(lhsElsSuffix)
          assert(elsCtxs.allCondsSet.contains(negCodeOf(lhsCond)))
          val elsRes = rec(resCtxs2, lhsElsCr.ctxs, lhsElsCr.terminal, rhsCtxs, rhs, elsCtxs, true)
          val (_, elsPlugged) = elsRes.selfPlugged(resCtxs2.withNegatedCond(lhsCond))

          resultOfIf(lhsCond, thnPlugged, elsPlugged, resCtxs2)

        case (IntLikeLitSig(b1), IntLikeLitSig(b2)) =>
          val r = b2c(rel match {
            case Label.Equals => b1 == b2
            case Label.GreaterEquals => b1 >= b2
            case Label.LessEquals => b1 <= b2
            case Label.LessThan => b1 < b2
            case Label.GreaterThan => b1 > b2
          })
          CodeRes(r, resCtxs.addBoundDef(lhs).addBoundDef(rhs).addBoundDef(r))

        case _ =>
          val r =
            if (rel == Label.Equals && provablyNeq(lhs, rhs)) falseCode
            else if (implied(relCode)(using env, resCtxs)) trueCode
            else if (implied(negCodeOf(relCode))(using env, resCtxs)) falseCode
            else relCode
          CodeRes(r, resCtxs.addBoundDef(lhs).addBoundDef(rhs).addBoundDef(r))
      }
    }

    val lhsCtxs = addDefinitions(pre, lhs)
    val rhsCtxs = addDefinitions(lhsCtxs, rhs)
    val res = rec(pre, lhsCtxs, lhs, rhsCtxs, rhs, cr.ctxs, true)
    res
  }

  final def adtSelect(recv: Code, lab: Label.ADTSelector, tpe: Type): Code = {
    code2sig(recv) match {
      case Signature(Label.ADT(id, _), args) if id == lab.ctor.id =>
        // In some cases, it may happen that id != ctor.id (hence the above guard).
        // e.g.:
        //  None() match {
        //    case Some(r) =>
        //      /* usage of r will result in id != ctor.id */
        //    case None() =>
        //  }
        // It's only later on that this branch will be eliminated.
        // Before then, fear not and do not panic! Let us only return the result, unchanged...
        val index = lab.ctor.definition.selectorID2Index(lab.selector)
        args(index)
      case _ => codeOfSig(mkADTSelector(recv, lab.adt, lab.ctor, lab.selector), tpe)
    }
  }

  final def tupleSelect(recv: Code, i: Int, tpe: Type): Code = {
    assert(i >= 1)
    code2sig(recv) match {
      case Signature(Label.Tuple, args) => args(i - 1)
      case _ => codeOfSig(mkTupleSelect(recv, i), tpe)
    }
  }

  // Flatten & constant folding, top-level
  final def flattenAssocArith(op: Label.Plus.type | Label.Times.type, lhs: Code, rhs: Code): Code = {
    assert(codeTpe(lhs) == codeTpe(rhs))
    val tpe = codeTpe(lhs)
    val neutral = if (op == Label.Plus) 0 else 1

    def flatten(c: Code): Seq[Code] = code2sig(c) match {
      case Signature(`op`, Seq(c1, c2)) => flatten(c1) ++ flatten(c2)
      case _ => Seq(c)
    }
    def cstFold(remaining: Seq[Code], acc: Seq[Code], cst: BigInt): (Seq[Code], BigInt) = remaining match {
      case Seq() => (acc, cst)
      case h +: rest => code2sig(h) match {
        case IntLikeLitSig(c) =>
          if (op == Label.Plus) cstFold(rest, acc, cst + c)
          else {
            if (c == 0) (Seq.empty, 0)
            else cstFold(rest, acc, cst * c)
          }
        case _ => cstFold(rest, acc :+ h, cst)
      }
    }
    def recons(terms0: Seq[Code], sort: Boolean): Code = {
      assert(terms0.nonEmpty)
      if (terms0.size == 1) terms0.head
      else {
        val terms = if (sort) terms0.sorted else terms0
        val sig = if (op == Label.Plus) mkPlus(terms) else mkTimes(terms)
        codeOfSig(sig, tpe)
      }
    }

    val terms = flatten(lhs) ++ flatten(rhs)
    val (nonLits, cst) = cstFold(terms, Seq.empty, neutral)
    lazy val cstCode = codeOfIntLit(cst, tpe)
    if (nonLits.isEmpty) cstCode
    else if (terms == nonLits && cst == neutral) {
      // If we hadn't done anything, we return the original one (without sorting) because otherwise we would
      // trouble (in some cases) our dear SMT solvers when mixing multiplication and additions...
      recons(Seq(lhs, rhs), sort = false)
    }
    else if (cst == neutral) recons(nonLits, sort = true)
    else recons(nonLits :+ cstCode, sort = true)
  }

  final def isIntLikeType(c: Code): Boolean = codeTpe(c) match {
    case BVType(_, _) => true
    case IntegerType() => true
    case _ => false
  }

  final def toLinComb(c: Code): LinComb = code2linCombLru.cached(c, {
    val tpe = codeTpe(c)
    assert(isIntLikeType(c))
    code2sig(c) match {
      case Signature(Label.Plus, terms) =>
        terms.foldLeft(LinComb.empty(tpe))(_ + toLinComb(_))
      case MinusSig(lhs, rhs) => toLinComb(lhs) - toLinComb(rhs)
      case Signature(Label.UMinus, Seq(c2)) => -toLinComb(c2)
      case IntLikeLitSig(l) => LinComb(Map.empty, l, tpe)
      case Signature(Label.Times, terms) =>
        val (fcts, vars) = terms.partitionMap(t => code2sig(t) match {
          case IntLikeLitSig(l) => Left(l)
          case _ => Right(t)
        })
        val fct = fcts.foldLeft(BigInt(1))(_ * _)
        val varsCode = if (vars.size == 1) vars.head else codeOfSig(mkTimes(vars), tpe)
        LinComb(Map(varsCode -> fct), 0, tpe)
      case _ => LinComb(Map(c -> 1), 0, tpe)
    }
  })

  final def fromLinComb(l: LinComb): Code = linComb2codeLru.cached(l, {
    val terms = l.terms.map { case (c, fct) =>
      if (fct == 1) c
      else if (fct == -1) codeOfSig(mkUMinus(c), l.tpe)
      else {
        // Note: fct == 0 should not appear
        val fctC = codeOfLit(intLitOfType(fct, l.tpe))
        codeOfSig(mkTimes(fctC, c), l.tpe)
      }
    }.toSeq
    lazy val termsC = if (terms.size == 1) terms.head else codeOfSig(mkPlus(terms), l.tpe)
    lazy val cstC = codeOfLit(intLitOfType(l.cst, l.tpe))
    if (terms.isEmpty) cstC
    else if (l.cst < 0) {
      val cstC2 = codeOfLit(intLitOfType(-l.cst, l.tpe))
      codeOfSig(mkMinus(termsC, cstC2), l.tpe)
    }
    else if (l.cst == 0) termsC
    else codeOfSig(mkPlus(terms :+ cstC), l.tpe)
  })

  enum SimplifiedCase {
    case Unreachable
    case Covered(caseCtxs: Ctxs, rhsCtxs: Ctxs, comp: Occurrences)
    case Unchanged(caseCtxs: Ctxs, rhsCtxs: Ctxs, caseConds: Seq[Code], comp: Occurrences)
  }

  enum SimplifiedCases {
    case Empty
    case ElidableMatchExpr(rhs: CodeRes)
    case Cases(res: Seq[CodeResMatchCase])
  }

  final def simplifyCase(scrut: Code, matchCase: LabMatchCase)(using env: Env, ctxs0: Ctxs): SimplifiedCase = {
    assert(ctxs0.isLitVarOrBoundDef(scrut))
    val PatBdgsAndConds(ctxs1, _, patConds) = addPatternBindingsAndConds(ctxs0, scrut, matchCase.pattern)
    val rhsCtxs = ctxs1.withCond(matchCase.guard)
    val caseConds = patConds :+ matchCase.guard

    lazy val guardComp = occurrencesOf(matchCase.guard)(using env, ctxs1)
    lazy val bodyComp = occurrencesOf(matchCase.rhs)(using env, rhsCtxs)
    lazy val unchanged = SimplifiedCase.Unchanged(ctxs0, rhsCtxs, caseConds, guardComp ++ bodyComp)

    if (caseConds.forall(c => codePurity(c).isPure)) {
      val caseCondsConj = conjunct(caseConds)
      lazy val negCondsConj = negatedConjunction(caseConds)
      if (implied(caseCondsConj)) SimplifiedCase.Covered(ctxs0, rhsCtxs, guardComp ++ bodyComp)
      else if (implied(negCondsConj)) SimplifiedCase.Unreachable
      else unchanged
    } else unchanged
  }

  final def simplifyCases(scrut: Code, cases: Seq[LabMatchCase])(using env: Env, ctxs: Ctxs): SimplifiedCases = {
    assert(ctxs.isLitVarOrBoundDef(scrut))

    def mkElidable(caseRhs: Code, caseCtxs: Ctxs, rhsCtxs: Ctxs): SimplifiedCases.ElidableMatchExpr = {
      assert(ctxs.isPrefixOf(caseCtxs))
      assert(caseCtxs.isPrefixOf(rhsCtxs))
      val Some((rhsUnpl, _)) = unplugged(caseRhs)(using env, rhsCtxs): @unchecked
      assert(rhsCtxs.isPrefixOf(rhsUnpl.ctxs))
      // Here, we remove all `Assumed` coming from the guard and the pattern.
      // These are not needed anymore because we will simplify the match expression away.
      val rhsUnplCtxs = caseCtxs.addExtraWithoutAssumed(rhsUnpl.ctxs)
      SimplifiedCases.ElidableMatchExpr(CodeRes(rhsUnpl.terminal, rhsUnplCtxs))
    }

    def acc2cases(acc: Seq[(LabMatchCase, Ctxs, Ctxs, Occurrences)]): Seq[CodeResMatchCase] =
      acc.map { case (lmc, _, _, occ) => CodeResMatchCase(lmc, occ) }

    def rec(cases: Seq[LabMatchCase], acc: Seq[(LabMatchCase, Ctxs, Ctxs, Occurrences)])(using ctxs: Ctxs): SimplifiedCases = cases match {
      case Seq() =>
        acc match {
          case Seq() => SimplifiedCases.Empty
          case Seq((soleCase, caseCtxs, rhsCtxs, _)) => mkElidable(soleCase.rhs, caseCtxs, rhsCtxs)
          case (fst, caseCtxs, fstCtxs, _) +: rest =>
            val allSameBodies = rest.forall(_._1.rhs == fst.rhs)
            if (allSameBodies) mkElidable(fst.rhs, caseCtxs, fstCtxs)
            else SimplifiedCases.Cases(acc2cases(acc))
        }
      case currCase +: rest =>
        simplifyCase(scrut, currCase) match {
          case SimplifiedCase.Unreachable => rec(rest, acc)
          case SimplifiedCase.Covered(caseCtxs, rhsCtxs, comp) =>
            if (acc.isEmpty) {
              mkElidable(currCase.rhs, caseCtxs, rhsCtxs)
            } else {
              val wildcard = LabMatchCase(LabelledPattern.Wildcard, currCase.guard, currCase.rhs)
              SimplifiedCases.Cases(acc2cases(acc) :+ CodeResMatchCase(wildcard, comp))
            }
          case SimplifiedCase.Unchanged(caseCtxs, rhsCtxs, caseConds, comp) =>
            val negCaseConds = negatedConjunction(caseConds)
            rec(rest, acc :+ (currCase, caseCtxs, rhsCtxs, comp))(using ctxs.withCond(negCaseConds))
        }
    }

    rec(cases, Seq.empty)
  }
  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Purity

  final def codePurity(c: Code)(using env: Env, ctxs: Ctxs): Purity =
    codePurityInst.codePurity(c)(using env.copy(forceBinding = true))

  final class CodePurity extends CodeTryFolder[Unit, Purity] {
    override type Extra = Unit

    private val visitingFns = mutable.Set.empty[Identifier]
    private val purityCache = mutable.Map.empty[Identifier, Boolean]
    private val fnBlockedBy = mutable.Map.empty[Identifier, Set[Identifier]] // K = fn blocked by fn in V
    private val codeBlockedBy = mutable.Map.empty[Code, Set[Identifier]] // K = code blocked by fns in V
    private val blocking = mutable.Map.empty[Identifier, (Set[Identifier], Set[Code])] // K = fn blocking fn and codes in V
    private val alreadyVisiting = mutable.Set.empty[Code]

    private val codePurityCacheThreshold = 10000
    private val codePurityCache = mutable.Map.empty[(Env, Ctxs, Code), Boolean]

    def codePurity(c: Code)(using env: Env, ctxs: Ctxs): Purity = {
      codePurityCache.get((env, ctxs, c)) match {
        case Some(p) => return Purity.fromBoolean(p)
        case None => ()
      }
      val res = tryFold(c, Pure, ()).map(_._1).getOrElse(Impure)
      res match {
        case Purity.Pure => codePurityCache += (env, ctxs, c) -> true
        case Purity.Impure => codePurityCache += (env, ctxs, c) -> false
        case Purity.Delayed(_) => ()
      }
      res
    }

    def functionsPurity(): Map[Identifier, Boolean] = purityCache.toMap

    def setFunctionPurityCache(fnPurityCache: Map[Identifier, Boolean]): Unit =
      purityCache ++= fnPurityCache

    def clearCaches(): Unit = {
      if (codePurityCache.size > codePurityCacheThreshold) {
        codePurityCache.clear()
      }
    }

    override def tryFoldPatternConditions(patConds: Seq[Code], acc: Purity, extra: Unit)(using Env, Ctxs): Either[Unit, Purity] = {
      val patCondsPurity = patConds.foldLeft(acc)(_ ++ codePurity(_))
      patCondsPurity match {
        case Impure => Left(())
        case p => Right(p)
      }
    }

    override def tryFoldImpl(c: Code, acc: Purity, extra: Unit)(using env: Env, ctxs: Ctxs): Either[Unit, (Purity, CodeRes)] = {
      if (acc == Impure) Left(())
      else if (ctxs.isBoundDef(c)) Right((acc, CodeRes(c, ctxs)))
      else {
        if (alreadyVisiting(c)) {
          alreadyVisiting -= c
          return Left(()) // May happen due to the isConstructor call below, which calls implies, etc.
        }
        alreadyVisiting += c

        // CodeRes + purity, but without `acc`
        // (we could have included `acc` in the recursive calls
        // but it's easy to forget it, so we add it at the end)
        val res = code2sig(c) match {
          case Signature(Label.Var(_) | Label.Lit(_), Seq()) => Right((Pure, CodeRes(c, ctxs)))
          case Signature(Label.Assume, Seq(pred, _)) =>
            assert(CodeRes.isTerminal(pred))
            if (pred == trueCode) super.tryFoldImpl(c, Pure, ())
            else Left(())

          case Signature(Label.Assert | Label.Require, Seq(pred, _)) =>
            assert(CodeRes.isTerminal(pred))
            val p = if (pred == trueCode) Pure else assmChkPurity
            super.tryFoldImpl(c, p, ())

          case Signature(Label.Ensuring, Seq(_, pred)) =>
            code2sig(pred) match {
              case Signature(Label.Lambda(Seq(_)), Seq(`trueCode`)) => super.tryFoldImpl(c, Pure, ())
              case _ => Left(())
            }

          case Signature(Label.ADTSelector(adt, ctor, _), Seq(e)) =>
            assert(CodeRes.isTerminal(e))
            if (opts.assumeChecked || isConstructor(e, adt, ctor.id).contains(true)) super.tryFoldImpl(c, Pure, ())
            else Left(())

          case Signature(Label.ADT(id, tps), args) =>
            assert(args.forall(CodeRes.isTerminal))
            // TODO: Ok? There is a comment in SimplifierWithPC...
            val ctor: TypedADTConstructor = getConstructor(id, tps)
            val consingPurity = {
              if (opts.assumeChecked || !ctor.sort.definition.hasInvariant) Pure
              else Impure
            }
            super.tryFoldImpl(c, consingPurity, ())

          case Signature(Label.Lambda(_), Seq(_)) => Right((Pure, CodeRes(c, ctxs.addBoundDef(c))))

          case Signature(Label.FunctionInvocation(id, _), _) =>
            super.tryFoldImpl(c, fnPurity(id), ())

          case Signature(Label.Application, callee +: args) =>
            assert(CodeRes.isTerminal(callee))
            assert(args.forall(CodeRes.isTerminal))
            // TODO: SimplifierWithPC ignores the callee purity for some reasons...
            lazy val calleePurity = code2sig(callee) match {
              case Signature(Label.Lambda(params), Seq(body)) =>
                assert(params.size == args.size)
                // The ctxs in which the lambda has been defined: we lookup in its body
                // (if we instead recur on the lambda itself, we will get Pure, which is not what we want here)
                val lambdaCtxs = ctxs.takeUntilDefined(callee)
                codePurity(body)(using env.inc, lambdaCtxs)
              case _ =>
                def rec(recv: Code): Purity = code2sig(recv) match {
                  case Signature(Label.Var(_), Seq()) =>
                    // It's a free var, and we do not know anything about it... (mimicking what SimplifierWithPC does)
                    // (ditto for field selection)
                    Pure
                  case Signature(Label.ADTSelector(_, ctor, _), Seq(recv)) if !ctor.sort.definition.hasInvariant =>
                    rec(recv)
                  case _ => Impure
                }
                rec(callee)
            }
            super.tryFoldImpl(c, assmChkPurity ++ calleePurity, ())

          case Signature(Label.Choose(v), Seq(pred)) =>
            if (pred == trueCode && hasInstance(varTpe(v)).contains(true)) Right((Pure, CodeRes(c, ctxs.addBoundDef(c))))
            else Left(())

          // TODO: What is the purity for NoTree/Error? In SimplifierWithPC and isImpure, there is no mention of NoTree/Error...
          case Signature(Label.Division | Label.Remainder | Label.Modulo | Label.NoTree(_) | Label.Error(_, _), _) =>
            super.tryFoldImpl(c, assmChkPurity, ())

          // TODO: Decreases, array select, map select?

          case _ => super.tryFoldImpl(c, Pure, ())
        }

        alreadyVisiting -= c

        // Purity, with `acc`
        val finalPurity = acc ++ res.map(_._1).getOrElse(Impure)
        finalPurity match {
          case Pure | Impure => ()
          case Delayed(blockers) =>
            codeBlockedBy += c -> blockers
            for (blocker <- blockers) {
              val (blockedFns, blockedCodes) = blocking.getOrElse(blocker, (Set.empty, Set.empty))
              blocking += blocker -> (blockedFns, blockedCodes + c)
            }
        }
        res.map { case (_, cr) => (finalPurity, cr) }
      }
    }

    def fnPurity(fn: Identifier): Purity = {
      def resolvedPurity(isPure: Boolean): Unit = {
        purityCache += fn -> isPure
        if (blocking.contains(fn)) {
          val (blockedFns, blockedCodes) = blocking.remove(fn).get
          for (blockedFn <- blockedFns) {
            assert(fnBlockedBy.contains(blockedFn))
            assert(fnBlockedBy(blockedFn) == Set(fn))
            fnBlockedBy -= blockedFn
            purityCache += blockedFn -> isPure
          }
          for (blockedCode <- blockedCodes) {
            assert(codeBlockedBy.contains(blockedCode))
            assert(codeBlockedBy(blockedCode) == Set(fn))
            codeBlockedBy -= blockedCode
          }
        }
      }

      def addToBlocked(blockers: Set[Identifier]): Unit = {
        assert(!blockers.contains(fn))
        // We add ourselves to the list of blocked peeps
        fnBlockedBy += fn -> blockers
        for (blocker <- blockers) {
          val (blockedFns, blockedCodes) = blocking.getOrElse(blocker, (Set.empty, Set.empty))
          blocking += blocker -> (blockedFns + fn, blockedCodes)
        }

        // We update the blocked ones to point towards the ones blocking us, and not us! We are shifting the blame.
        val (blockedFnsByThisFn, blockedCodeByThisCode) = blocking.remove(fn).getOrElse((Set.empty, Set.empty))
        for (blockedFn <- blockedFnsByThisFn) {
          assert(fnBlockedBy.contains(blockedFn))
          val upd = fnBlockedBy(blockedFn) - fn ++ blockers
          fnBlockedBy += blockedFn -> upd
        }
        for (blockedCode <- blockedCodeByThisCode) {
          assert(codeBlockedBy.contains(blockedCode))
          val upd = codeBlockedBy(blockedCode) - fn ++ blockers
          codeBlockedBy += blockedCode -> upd
        }
      }

      if (visitingFns.contains(fn)) {
        if (!opts.assumeChecked) Impure
        else Delayed(Set(fn))
      } else {
        purityCache.get(fn) match {
          case Some(true) => Pure
          case Some(false) => Impure
          case None if fnBlockedBy.contains(fn) => Delayed(fnBlockedBy(fn))
          case None =>
            given Env = Env(LambdaNesting(0), forceBinding = true)
            given Ctxs = Ctxs.empty
            given LetValSubst = LetValSubst.empty

            assert(!visitingFns.contains(fn))
            assert(!fnBlockedBy.contains(fn))
            assert(!blocking.contains(fn))
            visitingFns += fn
            val bodyCodeRes = codeOfFunctionBody(fn)
            val bodyCode = bodyCodeRes.selfPlugged(Ctxs.empty)._2
            val purity = codePurity(bodyCode)
            visitingFns -= fn
            purity match {
              case Pure =>
                resolvedPurity(isPure = true)
                Pure
              case Impure =>
                resolvedPurity(isPure = false)
                Impure
              case Delayed(blockers0) =>
                assert(blockers0.nonEmpty)
                assert(opts.assumeChecked)
                assert(!fnBlockedBy.contains(fn))
                val blockersWoCurr = blockers0 - fn

                if (blockers0.contains(fn)) {
                  assert(blocking.contains(fn))
                  if (blockersWoCurr.isEmpty) {
                    resolvedPurity(isPure = true)
                    Pure
                  } else {
                    addToBlocked(blockersWoCurr)
                    Delayed(blockersWoCurr)
                  }
                } else {
                  assert(!blocking.contains(fn))
                  addToBlocked(blockers0)
                  Delayed(blockers0)
                }
            }
        }
      }
    }
  }
  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Composition of codes, binding, inlining

  enum BindingCase {
    // In let v = e in body...
    case Elidable // ... the `e` (and the let) can be removed (that is, we can just return `body`, `e` is pure)
    case Inlinable // ... the `e` can be inlined or bound, but it definitely appears in `body` (may or may not be impure)
    case MustBind // ... the `e` must be bound (appears in `body` if pure, may not appear if impure)
  }

  final def isSimple(c: Code, bodyOccurrences: Occurrences)(using ctxs: Ctxs): Boolean = code2sig(c) match {
    case Signature(Label.Lit(_) | Label.Var(_), Seq()) => true
    case Signature(Label.IsConstructor(_, _) | Label.ADTSelector(_, _, _) | Label.TupleSelect(_) | Label.ArrayLength, Seq(recv)) =>
      isSimple(recv, bodyOccurrences) || !bodyOccurrences(recv).isMany
    case Signature(Label.ADT(_, _), args) => args.isEmpty
    case Signature(Label.ArraySelect, Seq(a, i)) =>
      (isSimple(a, bodyOccurrences) || !bodyOccurrences(a).isMany) && (isSimple(i, bodyOccurrences) || !bodyOccurrences(i).isMany)
    case Signature(Label.FunctionInvocation(id, _), args) => codePurityInst.fnPurity(id).isPure && args.forall(a => label(a).isUnitLiteral)
    case _ => false
  }

  final def mayDuplicate(c: Code, bodyOccurrences: Occurrences)(using ctxs: Ctxs): Boolean = code2sig(c) match {
    case _ if isSimple(c, bodyOccurrences) => true
    case Signature(Label.Equals | Label.GreaterEquals | Label.GreaterThan | Label.LessEquals | Label.LessThan
                   | Label.Plus | Label.Minus | Label.Times | Label.Division
                   | Label.Modulo | Label.Remainder
                   | Label.BVAnd | Label.BVOr | Label.BVXor | Label.BVShiftLeft
                   | Label.BVAShiftRight | Label.BVLShiftRight, args) => args.size <= 2 && args.forall(isSimple(_, bodyOccurrences))
    case Signature(Label.Not | Label.BVSignedToUnsigned | Label.BVUnsignedToSigned
                   | Label.BVNarrowingCast(_) | Label.BVWideningCast(_)
                   | Label.BVNot, Seq(e)) => isSimple(e, bodyOccurrences)
    case _ => false
  }

  final def needsBinding(terminal: Code, terminalComposition: Occurrences, bodyOccurrences: Occurrences)(using env: Env, prefix: Ctxs): BindingCase = {
    assert(!isLitOrVar(terminal))
    assert(!prefix.isBoundDef(terminal))

    code2sig(terminal) match {
      case Signature(Label.Ensuring, _) => BindingCase.Inlinable
      case _ =>
        if (env.forceBinding) BindingCase.MustBind
        else {
          val definitionOccurrence = bodyOccurrences(terminal)
          lazy val negatedDefOccurrence = negCodeCache.get(terminal).map(bodyOccurrences.apply).getOrElse(Occurrence.Zero)
          lazy val terminalIsPure = codePurity(terminal)
          definitionOccurrence match {
            case Occurrence.Many =>
              if (!isLambda(terminal) && mayDuplicate(terminal, bodyOccurrences)) BindingCase.Inlinable
              else BindingCase.MustBind
            case Occurrence.Zero =>
              // If an impure expressions does not appear in the body, we cannot eliminate it, we must therefore bind it
              if (!terminalIsPure.isPure && negatedDefOccurrence.isZero) BindingCase.MustBind
              else BindingCase.Elidable
            case Occurrence.Once(inCtxs, occurrenceNesting, _) if terminalIsPure.isPure =>
              assert(env.nesting.level <= occurrenceNesting.level)
              assert(prefix.impureParts.isPrefixOf(inCtxs))
              if (occurrenceNesting.level != env.nesting.level && terminalComposition.hasLambda) BindingCase.MustBind
              else BindingCase.Inlinable
            case Occurrence.Once(inCtxs, occurrenceNesting, _) =>
              // `inCtxs` represnts the active ctxs where `terminal` occurs.
              // If `inCtxs` is different from the ctxs where `terminal` is defined (that is, `prefix`), then we need to
              // bind it because inlining an impure expression after a path condition or other impure expressions is incorrect
              // (we need to preserve order of evaluation)

              assert(env.nesting.level <= occurrenceNesting.level)
              assert(prefix.impureParts.isPrefixOf(inCtxs))
              assert(prefix.impureParts.ctxs.size + 1 <= inCtxs.ctxs.size)
              assert(inCtxs.ctxs(prefix.impureParts.ctxs.size) == Ctx.BoundDef(terminal))

              if (env.nesting == occurrenceNesting && inCtxs.ctxs.size == prefix.impureParts.ctxs.size + 1) BindingCase.Inlinable
              else BindingCase.MustBind
          }
        }
    }
  }

  private val occOfInst = new occOf
  final def occurrencesOf(c: Code)(using env: Env, ctxs: Ctxs): Occurrences =
    occOfInst.tryFold(c, Occurrences.empty, ()).merge._1

  class occOf extends CodeTryFolder[Nothing, Occurrences] {
    override type Extra = Unit

    private val cacheThreshold = 10000
    private val cache = mutable.Map.empty[(Env, Ctxs, Code), (Occurrences, CodeRes)]

    def clearCaches(): Unit = {
      if (cache.size > cacheThreshold) {
        cache.clear()
      }
    }

    override def tryFoldPatternConditions(patConds: Seq[Code], acc: Occurrences, extra: Unit)
                                         (using Env, Ctxs): Either[Nothing, Occurrences] = Right(acc)

    override def tryFoldImpl(c: Code, acc: Occurrences, extra: Unit)
                            (using env: Env, ctxs: Ctxs): Either[Nothing, (Occurrences, CodeRes)] = {
      if (ctxs.isBoundDef(c)) Right((acc ++ Occurrences.of(c), CodeRes(c, ctxs)))
      else {
        val (occs, cr) = cache.getOrElseUpdate((env, ctxs, c), {
          if (!CodeRes.isTerminal(c)) {
            // Note: no Occurrences.of(c) because `c` is not a terminal
            pluggedOccMap.get((env, c)).flatMap(_.get(ctxs)) match {
              case Some((occs, cr)) => (occs, cr)
              case None =>
                val cr = tearDown(c)
                val (occs, plg) = cr.selfPlugged(ctxs)
                (occs, cr)
            }
          } else {
            // CodeRes + occurrences, but without acc
            // (we could have included `acc` in the recursive calls
            // but it's easy to forget it, so we add it at the end)
            val (occs, cr) = code2sig(c) match {
              case Signature(Label.Lit(_), Seq()) => (Occurrences.empty, CodeRes(c, ctxs))
              case Signature(Label.Var(_), Seq()) => (Occurrences.of(c), CodeRes(c, ctxs))

              case Signature(Label.Application, callee +: args) =>
                assert(CodeRes.isTerminal(callee))
                assert(args.forall(CodeRes.isTerminal))
                val (occCallee0, calleeCr) = tryFold(callee, Occurrences.empty, ()).merge
                assert(occCallee0(callee) == Occurrence.Once(calleeCr.ctxs.impureParts, env.nesting, OccurrenceKind.Expanded))
                val occCallee = occCallee0.setAsApplied(callee)
                val (occArgs, resCr) = tryFoldArgs(args, codeTpe(c), occCallee, ())(mkApp(calleeCr.terminal, _))(using env, calleeCr.ctxs).merge
                (occArgs ++ Occurrences.of(resCr.terminal)(using env, resCr.ctxs), resCr)

              case _ =>
                val (occs, cr) = super.tryFoldImpl(c, Occurrences.empty, ()).merge
                (occs ++ Occurrences.of(cr.terminal)(using env, cr.ctxs), cr)
            }
            (occs, cr)
          }
        })
        Right((acc ++ occs, cr))
      }
    }
  }

  final def inlineLambda(argsSubst: Seq[(VarId, Code)], body: Code)(using env: Env, outerCtxs: Ctxs): CodeRes = {
    // Essentially, a freshener + simplifyTopLvl at each step
    object impl extends CodeTransformer {
      override type Extra = Unit

      override def transformImpl(c: Code, repl: Map[Code, Code], extra: Unit)(using env: Env, ctxs: Ctxs): CodeRes = code2sig(c) match {
        case Signature(lab: Label.LambdaLike, Seq(body)) if !ctxs.isBoundDef(c) => // We do not modify bound lambdas
          val freshParams = lab.params.map(v => v -> freshened(v))
          val freshParamsRepl = freshParams.map { case (old, nw) => codeOfVarId(old) -> codeOfVarId(nw) }.toMap
          val newLab = lab.replacedParams(freshParams.map(_._2))
          val newLam = codeOfSig(mkLambdaLike(newLab, body), codeTpe(c))
          val rec = super.transformImpl(newLam, repl ++ freshParamsRepl, ())
          simplifyTopLvl(ctxs, rec)

        case Signature(_, _) =>
          val rec = super.transformImpl(c, repl, ())
          simplifyTopLvl(ctxs, rec)
      }
    }

    val bodyTpe = codeTpe(body)
    assert(argsSubst.forall { case (_, arg) => outerCtxs.isLitVarOrBoundDef(arg) })
    val initRepl = argsSubst.map { case (param, arg) => codeOfVarId(param) -> arg }.toMap
    val inlined = impl.transform(body, initRepl, ())(using env, outerCtxs)
    assert(codeTpe(inlined.terminal) == bodyTpe)
    inlined
  }
  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Uncoding

  case class RevRes(expr: Expr, used: Set[VarId])

  case class RevEnv(revLetDefs: Map[Code, VarId]) {
    def withLetBounds(vs: Seq[(VarId, Code)]): RevEnv =
      RevEnv(revLetDefs ++ vs.map { case (v, c) => c -> v }.toMap)

    def withLetBounds(v: VarId, c: Code): RevEnv =
      RevEnv(revLetDefs + (c -> v))
  }

  object RevEnv {
    def empty: RevEnv = RevEnv(Map.empty)
  }

  object uncoder extends CodeUnfolder[RevRes] {
    override type Extra = RevEnv

    override def unfoldImpl(c: Code, renv: RevEnv)(using env: Env, ctxs: Ctxs): (RevRes, CodeRes) = {
      renv.revLetDefs.get(c) match {
        case Some(vIx) =>
          assert(ctxs.isLitVarOrBoundDef(c))
          val rres = RevRes(varId2Var(vIx), Set(vIx))
          return (rres, CodeRes(c, ctxs))
        case None => ()
      }

      code2sig(c) match {
        case Signature(Label.Not, Seq(e)) => uncodeOfNot(e, renv)

        case Signature(Label.Let, Seq(cE, cBody)) =>
          val (e, eCr) = unfold(cE, renv)
          val v = freshVarId("bdg", codeTpe(cE))
          val (body, bodyCr) = unfold(cBody, renv.withLetBounds(v, cE))(using env, eCr.ctxs)
          val res = RevRes(Let(new ValDef(varId2Var(v)), e.expr, body.expr), e.used ++ body.used)
          (res, bodyCr)

        case MatchExprSig(scrut, cases) =>
          val (eScrut, scrutCr) = unfold(scrut, renv)
          val (rcases, used) = uncodeOfCases(scrut, cases, renv)(using env, scrutCr.ctxs)
          val res = RevRes(MatchExpr(eScrut.expr, rcases), eScrut.used ++ used)
          (res, scrutCr.derived(c))

        case PassesSig(scrut, cases) =>
          val (eScrut, scrutCr) = unfold(scrut, renv)
          val (rcases, used) = uncodeOfCases(scrut, cases, renv)(using env, scrutCr.ctxs)
          assert(eScrut.expr.getType match {
            case TupleType(bases) => bases.length == 2
            case _ => false
          })
          val fst = symbols.tupleSelect(eScrut.expr, 1, true)
          val snd = symbols.tupleSelect(eScrut.expr, 2, true)
          val res = RevRes(Passes(fst, snd, rcases), eScrut.used ++ used)
          (res, scrutCr.derived(c))

        case _ => super.unfoldImpl(c, renv)
      }
    }

    /////////////////////////////////////////////////////////////////////////////////////////////////////////

    override def combineLet(e: RevRes, body: RevRes, renv: RevEnv): RevRes = sys.error("`let` are explicitly handled")

    override def combineNot(e: RevRes, renv: RevEnv): RevRes = sys.error("`not` are explicitly handled")

    override def combineCase(guard: RevRes, rhs: RevRes, renv: RevEnv): RevRes = sys.error("match expression are explicitly handled")

    override def combineMatch(scrut: RevRes, cases: Seq[RevRes], renv: RevEnv): RevRes = sys.error("match expression are explicitly handled")

    override def combinePasses(scrut: RevRes, cases: Seq[RevRes], renv: RevEnv): RevRes = sys.error("passes expression are explicitly handled")

    override def unfoldVar(v: VarId, renv: RevEnv): RevRes = RevRes(varId2Var(v), Set(v))

    override def unfoldLit[A](l: Literal[A], renv: RevEnv): RevRes = RevRes(l, Set.empty)

    override def combineEnsuring(body: RevRes, pred: RevRes, renv: RevEnv): RevRes = {
      val predLam = pred.expr match {
        case lam@Lambda(_, _) => lam
        case Let(v, lam@Lambda(_, _), predBody) if predBody == v.toVariable => lam
        case e => sys.error(s"Got $e")
      }
      RevRes(Ensuring(body.expr, predLam), body.used ++ pred.used)
    }

    override def combineAssumeLike(kind: Label.AssumeLike, pred: RevRes, body: RevRes, renv: RevEnv): RevRes = {
      val expr = kind match {
        case Label.Assume => Assume(pred.expr, body.expr)
        case Label.Assert => Assert(pred.expr, None, body.expr)
        case Label.Require => Require(pred.expr, body.expr)
        case Label.Decreases => Decreases(pred.expr, body.expr)
      }
      RevRes(expr, pred.used ++ body.used)
    }

    override def combineLambdaLike(kind: Label.LambdaLike, body: RevRes, renv: RevEnv): RevRes = {
      kind match {
        case Label.Lambda(params) =>
          val vds = params.map(v => new ValDef(varId2Var(v)))
          RevRes(Lambda(vds, body.expr), body.used)
        case Label.Choose(v) =>
          RevRes(Choose(new ValDef(varId2Var(v)), body.expr), body.used)
        case Label.Forall(params) =>
          val vds = params.map(v => new ValDef(varId2Var(v)))
          RevRes(Forall(vds, body.expr), body.used)
      }
    }

    override def combineIf(cond: RevRes, thn: RevRes, els: RevRes, renv: RevEnv): RevRes =
      RevRes(IfExpr(cond.expr, thn.expr, els.expr), cond.used ++ thn.used ++ els.used)

    override def combineOr(disjs: Seq[RevRes], renv: RevEnv): RevRes =
      RevRes(Or(disjs.map(_.expr)), disjs.flatMap(_.used).toSet)

    override def combineCtorAlike(lab: Label, args: Seq[RevRes], renv: RevEnv): RevRes = {
      val eargs = args.map(_.expr)
      val expr = lab match {
        case Label.Tuple => Tuple(eargs)
        case Label.ADT(id, tps) => ADT(id, tps, eargs)
        case Label.ADTSelector(_, _, sel) =>
          val Seq(recv) = eargs
          ADTSelector(recv, sel)

        case Label.FunctionInvocation(id, tps) => FunctionInvocation(id, tps, eargs)
        case Label.Annotated(flags) =>
          val Seq(e) = eargs
          Annotated(e, flags)
        case Label.IsConstructor(_, id) =>
          val Seq(e) = eargs
          IsConstructor(e, id)
        case Label.Application =>
          val callee +: theArgs = eargs: @unchecked
          Application(callee, theArgs)

        case Label.Equals =>
          val Seq(lhs, rhs) = eargs
          Equals(lhs, rhs)
        case Label.LessThan =>
          val Seq(lhs, rhs) = eargs
          LessThan(lhs, rhs)
        case Label.GreaterThan =>
          val Seq(lhs, rhs) = eargs
          GreaterThan(lhs, rhs)
        case Label.LessEquals =>
          val Seq(lhs, rhs) = eargs
          LessEquals(lhs, rhs)
        case Label.GreaterEquals =>
          val Seq(lhs, rhs) = eargs
          GreaterEquals(lhs, rhs)
        case Label.UMinus =>
          val Seq(e) = eargs
          UMinus(e)
        case lab@(Label.Plus | Label.Times) =>
          assert(eargs.size >= 2)
          val recons: (Expr, Expr) => Expr = if (lab == Label.Plus) Plus.apply else Times.apply
          val e1 +: e2 +: rest = eargs: @unchecked
          rest.foldLeft(recons(e1, e2))(recons)
        case Label.Minus =>
          val Seq(lhs, rhs) = eargs
          Minus(lhs, rhs)
        case Label.Division =>
          val Seq(lhs, rhs) = eargs
          Division(lhs, rhs)
        case Label.Remainder =>
          val Seq(lhs, rhs) = eargs
          Remainder(lhs, rhs)
        case Label.Modulo =>
          val Seq(lhs, rhs) = eargs
          Modulo(lhs, rhs)
        case Label.BVNot =>
          val Seq(e) = eargs
          BVNot(e)
        case Label.BVAnd =>
          val Seq(lhs, rhs) = eargs
          BVAnd(lhs, rhs)
        case Label.BVOr =>
          val Seq(lhs, rhs) = eargs
          BVOr(lhs, rhs)
        case Label.BVXor =>
          val Seq(lhs, rhs) = eargs
          BVXor(lhs, rhs)
        case Label.BVShiftLeft =>
          val Seq(lhs, rhs) = eargs
          BVShiftLeft(lhs, rhs)
        case Label.BVAShiftRight =>
          val Seq(lhs, rhs) = eargs
          BVAShiftRight(lhs, rhs)
        case Label.BVLShiftRight =>
          val Seq(lhs, rhs) = eargs
          BVLShiftRight(lhs, rhs)
        case Label.BVNarrowingCast(newType) =>
          val Seq(e) = eargs
          BVNarrowingCast(e, newType)
        case Label.BVWideningCast(newType) =>
          val Seq(e) = eargs
          BVWideningCast(e, newType)
        case Label.BVUnsignedToSigned =>
          val Seq(e) = eargs
          BVUnsignedToSigned(e)
        case Label.BVSignedToUnsigned =>
          val Seq(e) = eargs
          BVSignedToUnsigned(e)
        case Label.TupleSelect(index) =>
          val Seq(e) = eargs
          TupleSelect(e, index)

        case Label.StringConcat =>
          val Seq(lhs, rhs) = eargs
          StringConcat(lhs, rhs)
        case Label.SubString =>
          val Seq(expr, start, end) = eargs
          SubString(expr, start, end)
        case Label.StringLength =>
          val Seq(expr) = eargs
          StringLength(expr)

        case Label.FiniteSet(base) => FiniteSet(eargs, base)
        case Label.SetAdd =>
          val Seq(set, elem) = eargs
          SetAdd(set, elem)
        case Label.ElementOfSet =>
          val Seq(elem, set) = eargs
          ElementOfSet(elem, set)
        case Label.SubsetOf =>
          val Seq(lhs, rhs) = eargs
          SubsetOf(lhs, rhs)
        case Label.SetIntersection =>
          val Seq(lhs, rhs) = eargs
          SetIntersection(lhs, rhs)
        case Label.SetUnion =>
          val Seq(lhs, rhs) = eargs
          SetUnion(lhs, rhs)
        case Label.SetDifference =>
          val Seq(lhs, rhs) = eargs
          SetDifference(lhs, rhs)

        case Label.FiniteArray(base) => FiniteArray(eargs, base)
        case Label.LargeArray(elemsIndices, base) =>
          val elems :+ default :+ size = eargs: @unchecked
          LargeArray(elemsIndices.zip(elems).toMap, default, size, base)
        case Label.ArraySelect =>
          val Seq(arr, i) = eargs
          ArraySelect(arr, i)
        case Label.ArrayUpdated =>
          val Seq(arr, i, v) = eargs
          ArrayUpdated(arr, i, v)
        case Label.ArrayLength =>
          val Seq(arr) = eargs
          ArrayLength(arr)

        case Label.FiniteMap(keyTpe, valueTpe) =>
          val exprElems :+ exprDefault = eargs: @unchecked
          val paired = exprElems.grouped(2).map { case Seq(k, v) => (k, v) }.toSeq
          FiniteMap(paired, exprDefault, keyTpe, valueTpe)
        case Label.MapApply =>
          val Seq(map, k) = eargs
          MapApply(map, k)
        case Label.MapUpdated =>
          val Seq(map, k, v) = eargs
          MapUpdated(map, k, v)

        case Label.Error(tpe, descr) => Error(tpe, descr)
        case Label.NoTree(tpe) => NoTree(tpe)

        case lab => sys.error(s"uncodeOf: what is this: $lab")
      }
      RevRes(expr, args.flatMap(_.used).toSet)
    }

    /////////////////////////////////////////////////////////////////////////////////////////////////////////

    def uncodeOfNot(c: Code, renv: RevEnv)(using env: Env, ctxs: Ctxs): (RevRes, CodeRes) = {
      code2sig(c) match {
        case Signature(Label.Or, fst +: rest) if !renv.revLetDefs.contains(c) =>
          val (fstRR0, fstCr) = unfold(fst, renv)
          assert(fstCr.terminal == fst)
          val fstRR = RevRes(not(fstRR0.expr), fstRR0.used)
          val rrs = rest.foldLeft((Seq(fstRR), fstCr.ctxs.withNegatedCond(fstCr.terminal))) {
            case ((accRR, ctxs), disj) =>
              given Ctxs = ctxs
              val (disjRR0, disjCr) = unfold(disj, renv)
              val disjRR = RevRes(not(disjRR0.expr), disjRR0.used)
              (accRR :+ disjRR, disjCr.ctxs.withNegatedCond(disjCr.terminal))
          }._1
          val rr = RevRes(And(rrs.map(_.expr)), rrs.flatMap(_.used).toSet)
          val cr = fstCr.derived(c).derived(codeOfSig(mkNot(c), BoolTy))
          (rr, cr)

        case _ =>
          val (res, cr) = unfold(c, renv)
          (RevRes(Not(res.expr), res.used), cr.derived(codeOfSig(mkNot(c), BoolTy)))
      }
    }

    def convertPattern(scrut: Code, pat: LabelledPattern, vds: Map[Code, ValDef]): Pattern = {
      def recHelper(subscruts: Seq[Code], subps: Seq[LabelledPattern]): Seq[Pattern] = {
        assert(subscruts.size == subps.size)
        subscruts.zip(subps).map {
          case (subscrut, subpat) => convertPattern(subscrut, subpat, vds)
        }
      }

      val bdg = vds.get(scrut)
      pat match {
        case LabelledPattern.Wildcard => WildcardPattern(bdg)
        case LabelledPattern.ADT(id, tps, subps) =>
          val rsubs = recHelper(adtSubScrutinees(scrut, ADTType(id, tps)), subps)
          ADTPattern(bdg, id, tps, rsubs)
        case LabelledPattern.TuplePattern(subps) =>
          val tt@TupleType(bases) = codeTpe(scrut): @unchecked
          assert(bases.size == subps.size)
          val rsubs = recHelper(tupleSubscrutinees(scrut, tt), subps)
          TuplePattern(bdg, rsubs)
        case LabelledPattern.Lit(lit) => LiteralPattern(bdg, lit)
        case LabelledPattern.Unapply(recs, id, tps, subps) =>
          assert(recs.isEmpty)
          val rsubs = recHelper(unapplySubScrutinees(scrut, id, tps).subs, subps)
          UnapplyPattern(bdg, Seq.empty, id, tps, rsubs)
      }
    }

    case class UncodedCase(pat: Pattern, guard: RevRes, rhs: RevRes, caseConds: Seq[Code])

    def uncodeOfCase(cScrut: Code, cse: LabMatchCase, renv0: RevEnv)(using env: Env, ctxs0: Ctxs): UncodedCase = {
      val PatBdgsAndConds(ctxs1, allScruts, patConds) = addPatternBindingsAndConds(ctxs0, cScrut, cse.pattern)
      val scrutBdgs = allScruts.zipWithIndex.map {
        case (subScrut, i) =>
          val vId = idOfVariable(Variable.fresh(s"bdg$i", codeTpe(subScrut)))
          vId -> subScrut
      }
      val renv1 = renv0.withLetBounds(scrutBdgs)
      val (rguard, _) = unfold(cse.guard, renv1)(using env, ctxs1)
      val ctxsForRhs = ctxs1.withCond(cse.guard)
      val (rrhs, _) = unfold(cse.rhs, renv1)(using env, ctxsForRhs)
      // We remove unneeded scrut. bindings
      val scrutVds = scrutBdgs.filter { case (v, _) => rguard.used(v) || rrhs.used(v) }
        .map { case (v, c) =>
          val vd = new ValDef(varId2Var(v))
          c -> vd
        }.toMap
      val convertedPattern = convertPattern(cScrut, cse.pattern, scrutVds)
      UncodedCase(convertedPattern, rguard, rrhs, patConds :+ cse.guard)
    }

    def uncodeOfCases(cScrut: Code, cases: Seq[LabMatchCase], renv: RevEnv)
                     (using env: Env, ctxs: Ctxs): (Seq[MatchCase], Set[VarId]) = {
      def rec(cases: Seq[LabMatchCase], transformedCases: Seq[MatchCase], used: Set[VarId])
             (using ctxs: Ctxs): (Seq[MatchCase], Set[VarId]) = cases match {
        case Seq() => (transformedCases, used)
        case cse +: rest =>
          val uncoded = uncodeOfCase(cScrut, cse, renv)
          val negCaseConds = negatedConjunction(uncoded.caseConds)
          val theGuard =
            if (uncoded.guard.expr == BooleanLiteral(true)) None
            else Some(uncoded.guard.expr)
          val theCase = MatchCase(uncoded.pat, theGuard, uncoded.rhs.expr)
          val newUsed = used ++ uncoded.guard.used ++ uncoded.rhs.used
          rec(rest, transformedCases :+ theCase, newUsed)(using ctxs.withCond(negCaseConds))
      }
      rec(cases, Seq.empty, Set.empty)
    }
  }

  final def uncodeOf(c: Code)(using Env, Ctxs): RevRes = uncoder.unfold(c, RevEnv.empty)._1

  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Code transformer & folder

  trait CodeTransformer {
    type Extra

    final def transform(c: Code, repl: Map[Code, Code], extra: Extra)(using env: Env, ctxs: Ctxs): CodeRes = {
      val res = repl.get(c) match {
        case Some(cc) =>
          assert(ctxs.isLitVarOrBoundDef(cc), "repl refers to a code that was not bound!!!")
          CodeRes(cc, ctxs)
        case None =>
          transformImpl(c, repl, extra)
      }
      assert(ctxs.isPrefixOf(res.ctxs))
      res
    }

    def transformImpl(c: Code, repl: Map[Code, Code], extra: Extra)(using env: Env, ctxs: Ctxs): CodeRes = {
      val tpe = codeTpe(c)
      assert(!repl.contains(c), s"$c = ${code2sig(c)} has not been replaced by transform")

      code2sig(c) match {
        case Signature(Label.Var(_) | Label.Lit(_), Seq()) => CodeRes(c, ctxs)

        case Signature(Label.Let, Seq(e, b)) if ctxs.isBoundDef(e) =>
          transform(b, repl, extra)

        case Signature(Label.Let, Seq(e, b)) =>
          assert(CodeRes.isTerminal(e))
          assert(!isLitOrVar(e))
          val re = transform(e, repl, extra)
          assert(re.ctxs.isLitVarOrBoundDef(re.terminal))
          transform(b, repl + (e -> re.terminal), extra)(using env, re.ctxs)

        case Signature(Label.IfExpr, Seq(cond, thenn, els)) =>
          assert(CodeRes.isTerminal(cond))
          val rcond = transform(cond, repl, extra)
          val thennCtxs = rcond.ctxs.withCond(rcond.terminal)
          val rthenn = transform(thenn, repl, extra)(using env, thennCtxs)
          val elsCtxs = rcond.ctxs.withNegatedCond(rcond.terminal)
          val rels = transform(els, repl, extra)(using env, elsCtxs)
          CodeRes.ifExpr(rcond, rthenn, rels, tpe)

        case Signature(lab: Label.LambdaLike, Seq(body)) =>
          val rbody = transform(body, repl, extra)(using env.incIf(lab))
          CodeRes.lambdaLike(lab, rbody, tpe)

        case Signature(lab: Label.AssumeLike, Seq(pred, body)) =>
          assert(CodeRes.isTerminal(pred))
          val rpred = transform(pred, repl, extra)
          assert(rpred.ctxs.isLitVarOrBoundDef(rpred.terminal))
          transform(body, repl, extra)(using env, rpred.ctxs.withAssumeLike(lab, rpred.terminal))

        case Signature(Label.Ensuring, Seq(body, pred)) =>
          val rbody = transform(body, repl, extra)
          val rpred = transform(pred, repl, extra)
          CodeRes.ensuring(rbody, rpred, tpe)

        case Signature(Label.Or, disjs) =>
          transformDisjunction(disjs)(transform(_, repl, extra))

        case Signature(Label.Not, Seq(n)) =>
          val rn = transform(n, repl, extra)
          rn.derived(negCodeOf(rn.terminal))

        case Signature(Label.Error(ofTpe, descr), Seq()) =>
          CodeRes.err(ofTpe, descr, tpe)
        case Signature(Label.NoTree(ofTpe), Seq()) =>
          CodeRes.noTree(ofTpe, tpe)

        case MatchExprSig(scrut, cases) =>
          val rscrut = transform(scrut, repl, extra)
          assert(rscrut.ctxs.isLitVarOrBoundDef(rscrut.terminal))
          val rcases = transformCases(scrut, rscrut.terminal, cases, repl + (scrut -> rscrut.terminal), extra, Seq.empty)(using env, rscrut.ctxs)
          CodeRes.matchExpr(rscrut, rcases, tpe)

        case PassesSig(scrut, cases) =>
          val rscrut = transform(scrut, repl, extra)
          assert(rscrut.ctxs.isLitVarOrBoundDef(rscrut.terminal))
          val rcases = transformCases(scrut, rscrut.terminal, cases, repl + (scrut -> rscrut.terminal), extra, Seq.empty)(using env, rscrut.ctxs)
          CodeRes.passes(rscrut, rcases, tpe)

        case Signature(lab, children) => transformSeq(children, tpe, repl, extra)(Signature(lab, _))
      }
    }

    final def transformSeq(cs: Seq[Code], tpe: Type, repl: Map[Code, Code], extra: Extra)
                          (mkSig: Seq[Code] => Signature)(using env: Env, ctxs: Ctxs): CodeRes = {
      given x_x: Ctxs = sys.error("Carefully select ctxs")
      val (newCtxs, ress) = cs.foldLeft((ctxs, Seq.empty[CodeRes])) {
        case ((ctxs, codeResAcc), c) =>
          assert(CodeRes.isTerminal(c))
          val res = transform(c, repl, extra)(using env, ctxs)
          assert(ctxs.isPrefixOf(res.ctxs))
          (res.ctxs, codeResAcc :+ res)
      }
      combineCodeRes(ress, tpe)(mkSig)(using env, newCtxs)
    }

    def transformCase(oldScrut: Code, newScrut: Code, matchCase: LabMatchCase, repl0: Map[Code, Code], extra: Extra)
                     (using env: Env, ctxs0: Ctxs): (CodeResMatchCase, Seq[Code]) = {
      assert(repl0.get(oldScrut) == Some(newScrut), s"'repl0' does not contain $oldScrut -> $newScrut")
      assert(ctxs0.isLitVarOrBoundDef(newScrut))

      val PatBdgsAndConds(ctxs1, newBdgs, patConds) = addPatternBindingsAndConds(ctxs0, newScrut, matchCase.pattern)
      val repl = {
        if (oldScrut == newScrut) repl0
        else {
          val PatBdgsAndConds(_, oldBdgs, _) = addPatternBindingsAndConds(ctxs0.addBoundDef(oldScrut), oldScrut, matchCase.pattern)
          assert(oldBdgs.size == newBdgs.size)
          repl0 ++ oldBdgs.zip(newBdgs).toMap
        }
      }

      val rguard = transform(matchCase.guard, repl, extra)(using env, ctxs1)
      val (compGuard, cGuard) = rguard.selfPlugged(ctxs1)

      val ctxsForRhs = ctxs1.withCond(cGuard)
      val rrhs = transform(matchCase.rhs, repl, extra)(using env, ctxsForRhs)
      val (compRhs, cRhs) = rrhs.selfPlugged(ctxsForRhs)

      val newMatchCase = LabMatchCase(matchCase.pattern, cGuard, cRhs)
      (CodeResMatchCase(newMatchCase, compGuard ++ compRhs), patConds :+ cGuard)
    }

    def transformCases(oldScrut: Code, newScrut: Code, cases: Seq[LabMatchCase],
                       repl: Map[Code, Code], extra: Extra,
                       acc: Seq[CodeResMatchCase])
                      (using env: Env, ctxs: Ctxs): Seq[CodeResMatchCase] = {
      if (cases.isEmpty) acc
      else {
        val (newMatchCase, caseConds) = transformCase(oldScrut, newScrut, cases.head, repl, extra)
        val negCaseConds = negatedConjunction(caseConds)
        transformCases(oldScrut, newScrut, cases.tail, repl, extra, acc :+ newMatchCase)(using env, ctxs.withCond(negCaseConds))
      }
    }
  }

  trait CodeTryFolder[E, T] {
    type Extra

    final def tryFold(c: Code, acc: T, extra: Extra)(using env: Env, ctxs: Ctxs): Either[E, (T, CodeRes)] = {
      tryFoldImpl(c, acc, extra) match {
        case Left(e) => Left(e)
        case Right((newAcc, cr)) =>
          assert(ctxs.isPrefixOf(cr.ctxs))
          assert(cr.ctxs.isLitVarOrBoundDef(cr.terminal))
          assert(!CodeRes.isTerminal(c) || cr.terminal == c)
          Right((newAcc, cr))
      }
    }

    def tryFoldImpl(c: Code, acc: T, extra: Extra)(using env: Env, ctxs: Ctxs): Either[E, (T, CodeRes)] = {
      val tpe = codeTpe(c)
      code2sig(c) match {
        case Signature(Label.Lit(_) | Label.Var(_), Seq()) => Right((acc, CodeRes(c, ctxs)))

        case Signature(Label.Let, Seq(e, b)) if ctxs.isBoundDef(e) =>
          tryFold(b, acc, extra)

        case Signature(Label.Let, Seq(e, b)) =>
          assert(CodeRes.isTerminal(e))
          assert(!isLitOrVar(e))
          for {
            resE <- tryFold(e, acc, extra)
            _ = assert(resE._2.ctxs.isBoundDef(e))
            resB <- tryFold(b, resE._1, extra)(using env, resE._2.ctxs)
          } yield resB

        case Signature(lab: Label.AssumeLike, Seq(pred, body)) =>
          assert(CodeRes.isTerminal(pred))
          for {
            resPred <- tryFold(pred, acc, extra)
            _ = assert(resPred._2.terminal == pred)
            resBody <- tryFold(body, resPred._1, extra)(using env, resPred._2.ctxs.withAssumeLike(lab, pred))
          } yield resBody

        case Signature(Label.IfExpr, Seq(cond, thn, els)) =>
          assert(CodeRes.isTerminal(cond))
          for {
            resCond <- tryFold(cond, acc, extra)
            _ = assert(resCond._2.terminal == cond)
            resThen <- tryFold(thn, resCond._1, extra)(using env, resCond._2.ctxs.withCond(cond))
            resEls <- tryFold(els, resThen._1, extra)(using env, resCond._2.ctxs.withNegatedCond(cond))
            resTerminal = codeOfSig(mkIfExpr(cond, thn, els), tpe)
            resCr = resCond._2.derived(resTerminal)
          } yield (resEls._1, resCr)

        case Signature(Label.Or, fst +: rest) =>
          assert(CodeRes.isTerminal(fst))
          for {
            resFst <- tryFold(fst, acc, extra)
            _ = assert(resFst._2.terminal == fst)
            initCtxs = resFst._2.ctxs.withNegatedCond(fst)
            resRest <- ocbsl.tryFoldLeft(rest, (resFst._1, initCtxs)) {
              case ((acc, ctxs), disj) =>
                given Ctxs = ctxs
                tryFold(disj, acc, extra).map {
                  case (newAcc, disjCr) =>
                    assert(disjCr.ctxs.isLitVarOrBoundDef(disjCr.terminal))
                    (newAcc, disjCr.ctxs.withNegatedCond(disjCr.terminal))
                }
            }
            resTerminal = codeOfDisjs(fst +: rest)
            resCr = resFst._2.derived(resTerminal)
          } yield (resRest._1, resCr)

        case Signature(Label.Not, Seq(n)) =>
          assert(CodeRes.isTerminal(n))
          tryFold(n, acc, extra)
            .map { case (acc, cr) =>
              val neg = codeOfSig(mkNot(cr.terminal), BoolTy)
              assert(cr.terminal == n)
              (acc, cr.derived(neg))
            }

        case Signature(Label.Ensuring, Seq(body, pred)) =>
          for {
            resBody <- tryFold(body, acc, extra)
            resPred <- tryFold(pred, resBody._1, extra)
          } yield (resPred._1, CodeRes(c, ctxs.addBoundDef(c)))

        case Signature(lab: Label.LambdaLike, Seq(body)) =>
          tryFold(body, acc, extra)(using env.incIf(lab), ctxs)
            .map { case (acc, _) => (acc, CodeRes(c, ctxs.addBoundDef(c))) }

        case MatchExprSig(scrut, cases) =>
          for {
            resScrut <- tryFold(scrut, acc, extra)
            _ = assert(resScrut._2.terminal == scrut)
            accCases <- tryFoldCases(scrut, cases, resScrut._1, extra)(using env, resScrut._2.ctxs)
            resTerminal = codeOfSig(mkMatchExpr(scrut, cases), tpe)
            resCr = resScrut._2.derived(resTerminal)
          } yield (accCases, resCr)

        case PassesSig(scrut, cases) =>
          for {
            resScrut <- tryFold(scrut, acc, extra)
            _ = assert(resScrut._2.terminal == scrut)
            accCases <- tryFoldCases(scrut, cases, resScrut._1, extra)(using env, resScrut._2.ctxs)
            resTerminal = codeOfSig(mkPasses(scrut, cases), tpe)
            resCr = resScrut._2.derived(resTerminal)
          } yield (accCases, resCr)

        case Signature(lab, args) =>
          assert(args.forall(CodeRes.isTerminal))
          tryFoldArgs(args, lab, tpe, acc, extra)
      }
    }

    final def tryFoldArgs(args: Seq[Code], tpe: Type, acc: T, extra: Extra)(cons: Seq[Code] => Signature)
                         (using env: Env, ctxs: Ctxs): Either[E, (T, CodeRes)] = {
      val folded = ocbsl.tryFoldLeft(args, (acc, ctxs, Seq.empty[CodeRes])) {
        case ((acc, ctxs, crs), arg) =>
          given Ctxs = ctxs
          assert(CodeRes.isTerminal(arg))
          tryFold(arg, acc, extra).map {
            case (newAcc, newCr) =>
              assert(newCr.terminal == arg)
              (newAcc, newCr.ctxs, crs :+ newCr)
          }
      }
      folded.map {
        case (acc, ctxs, crs) =>
          given Ctxs = ctxs
          val combined = combineCodeRes(crs, tpe)(cons)
          (acc, combined)
      }
    }

    final def tryFoldArgs(args: Seq[Code], lab: Label, tpe: Type, acc: T, extra: Extra)(using env: Env, ctxs: Ctxs): Either[E, (T, CodeRes)] =
      tryFoldArgs(args, tpe, acc, extra)(Signature(lab, _))

    final def tryFoldCase(scrut: Code, matchCase: LabMatchCase, acc: T, extra: Extra)
                         (using env: Env, ctxs0: Ctxs): Either[E, (T, Seq[Code])] = {
      val PatBdgsAndConds(ctxs1, _, patConds) = addPatternBindingsAndConds(ctxs0, scrut, matchCase.pattern)
      val ctxsForPatConds = ctxs0.addExtraWithoutAssumed(ctxs1) // Like ctxs1 but without pattern conds (expressed with `Assumed`)
      for {
        rpatConds <- tryFoldPatternConditions(patConds, acc, extra)(using env, ctxsForPatConds)
        rguard <- tryFold(matchCase.guard, rpatConds, extra)(using env, ctxs1)
        // As guard et rhs are self-plugged, we ignore their resulting ctxs
        ctxsForRhs = ctxs1.withCond(matchCase.guard)
        rrhs <- tryFold(matchCase.rhs, rguard._1, extra)(using env, ctxsForRhs)
      } yield (rrhs._1, patConds :+ matchCase.guard)
    }

    final def tryFoldCases(scrut: Code, cases: Seq[LabMatchCase], acc: T, extra: Extra)
                          (using env: Env, ctxs: Ctxs): Either[E, T] = {
      if (cases.isEmpty) Right(acc)
      else {
        tryFoldCase(scrut, cases.head, acc, extra).flatMap {
          case (rcase, caseConds) =>
            val negCaseConds = negatedConjunction(caseConds)
            tryFoldCases(scrut, cases.tail, rcase, extra)(using env, ctxs.withCond(negCaseConds))
        }
      }
    }

    def tryFoldPatternConditions(patConds: Seq[Code], acc: T, extra: Extra)(using Env, Ctxs): Either[E, T]
  }

  trait CodeUnfolder[T] {
    type Extra

    final def unfold(c: Code, extra: Extra)(using env: Env, ctxs: Ctxs): (T, CodeRes) = {
      val (t, cr) = unfoldImpl(c, extra)
      assert(ctxs.isPrefixOf(cr.ctxs))
      assert(!CodeRes.isTerminal(c) || cr.terminal == c)
      (t, cr)
    }

    def unfoldVar(v: VarId, extra: Extra): T

    def unfoldLit[A](l: Literal[A], extra: Extra): T

    def combineLet(e: T, body: T, extra: Extra): T

    def combineEnsuring(body: T, pred: T, extra: Extra): T

    def combineAssumeLike(kind: Label.AssumeLike, pred: T, body: T, extra: Extra): T

    def combineLambdaLike(kind: Label.LambdaLike, body: T, extra: Extra): T

    def combineIf(cond: T, thn: T, els: T, extra: Extra): T

    def combineNot(e: T, extra: Extra): T

    def combineOr(disjs: Seq[T], extra: Extra): T

    def combineCtorAlike(lab: Label, args: Seq[T], extra: Extra): T

    def combineCase(guard: T, rhs: T, extra: Extra): T

    def combineMatch(scrut: T, cases: Seq[T], extra: Extra): T

    def combinePasses(scrut: T, cases: Seq[T], extra: Extra): T

    def unfoldImpl(c: Code, extra: Extra)(using env: Env, ctxs: Ctxs): (T, CodeRes) = {
      val tpe = codeTpe(c)
      code2sig(c) match {
        case Signature(Label.Var(v), Seq()) => (unfoldVar(v, extra), CodeRes(c, ctxs))
        case Signature(Label.Lit(l), Seq()) => (unfoldLit(l, extra), CodeRes(c, ctxs))

        case Signature(Label.Let, Seq(e, body)) if ctxs.isBoundDef(e) => unfold(body, extra)

        case Signature(Label.Let, Seq(e, body)) =>
          val (te, eCr) = unfold(e, extra)
          val (tbody, bodyCr) = unfold(body, extra)(using env, eCr.ctxs)
          val tres = combineLet(te, tbody, extra)
          (tres, bodyCr)

        case Signature(kind: Label.AssumeLike, Seq(pred, body)) =>
          val (tpred, predCr) = unfold(pred, extra)
          assert(predCr.terminal == pred)
          val (tbody, bodyCr) = unfold(body, extra)(using env, predCr.ctxs.withAssumeLike(kind, pred))
          val tres = combineAssumeLike(kind, tpred, tbody, extra)
          (tres, bodyCr)

        case Signature(Label.IfExpr, Seq(cond, thn, els)) =>
          val (tcond, condCr) = unfold(cond, extra)
          assert(condCr.terminal == cond)
          val (tthen, _) = unfold(thn, extra)(using env, condCr.ctxs.withCond(cond))
          val (tels, _) = unfold(els, extra)(using env, condCr.ctxs.withNegatedCond(cond))
          val tres = combineIf(tcond, tthen, tels, extra)
          (tres, condCr.derived(c))

        case Signature(Label.Ensuring, Seq(body, pred)) =>
          val (tbody, _) = unfold(body, extra)
          val (tpred, _) = unfold(pred, extra)
          val tres = combineEnsuring(tbody, tpred, extra)
          (tres, CodeRes(c, ctxs.addBoundDef(c)))

        case Signature(kind: Label.LambdaLike, Seq(body)) =>
          val (tbody, _) = unfold(body, extra)(using env.incIf(kind), ctxs)
          val tres = combineLambdaLike(kind, tbody, extra)
          (tres, CodeRes(c, ctxs.addBoundDef(c)))

        case Signature(Label.Or, fst +: rest) =>
          assert(CodeRes.isTerminal(fst))
          val (tfst, fstCr) = unfold(fst, extra)
          assert(fstCr.terminal == fst)
          val tdisjs = rest.foldLeft((Seq(tfst), fstCr.ctxs.withNegatedCond(fst))) {
            case ((acc, ctxs), disj) =>
              given Ctxs = ctxs
              val (tdisj, disjCr) = unfold(disj, extra)
              (acc :+ tdisj, disjCr.ctxs.withNegatedCond(disjCr.terminal))
          }._1
          val tres = combineOr(tdisjs, extra)
          (tres, fstCr.derived(c))

        case Signature(Label.Not, Seq(e)) =>
          assert(CodeRes.isTerminal(e))
          val (te, cr) = unfold(e, extra)
          assert(cr.terminal == e)
          val tres = combineNot(te, extra)
          (tres, cr.derived(c))

        case MatchExprSig(scrut, cases) =>
          val (tscrut, scrutCr) = unfold(scrut, extra)
          assert(scrutCr.terminal == scrut)
          val tcases = unfoldCases(scrut, cases, extra)(using env, scrutCr.ctxs)
          val tres = combineMatch(tscrut, tcases, extra)
          (tres, scrutCr.derived(c))

        case PassesSig(scrut, cases) =>
          val (tscrut, scrutCr) = unfold(scrut, extra)
          assert(scrutCr.terminal == scrut)
          val tcases = unfoldCases(scrut, cases, extra)(using env, scrutCr.ctxs)
          val tres = combinePasses(tscrut, tcases, extra)
          (tres, scrutCr.derived(c))

        case Signature(lab, args) =>
          val (targsAndCrs, ctxs2) = unfoldArgs(args, extra)
          val (targs, argsCrs) = targsAndCrs.unzip
          val tres = combineCtorAlike(lab, targs, extra)
          val cr = combineCodeRes(argsCrs, tpe)(Signature(lab, _))(using env, ctxs2)
          (tres, cr)
      }
    }

    final def unfoldCase(scrut: Code, cse: LabMatchCase, extra: Extra)(using env: Env, ctxs0: Ctxs): (T, T, Seq[Code]) = {
      val PatBdgsAndConds(ctxs1, _, patConds) = addPatternBindingsAndConds(ctxs0, scrut, cse.pattern)
      val (tguard, _) = unfold(cse.guard, extra)(using env, ctxs1)
      val (trhs, _) = unfold(cse.rhs, extra)(using env, ctxs1.withCond(cse.guard))
      (tguard, trhs, patConds :+ cse.guard)
    }

    final def unfoldCases(scrut: Code, cases: Seq[LabMatchCase], extra: Extra)(using env: Env, ctxs: Ctxs): Seq[T] = {
      def rec(cases: Seq[LabMatchCase], acc: Seq[T])(using ctxs: Ctxs): Seq[T] = cases match {
        case Seq() => acc
        case cse +: rest =>
          val (tguard, trhs, caseConds) = unfoldCase(scrut, cse, extra)
          val negCaseConds = negatedConjunction(caseConds)
          rec(rest, acc :+ combineCase(tguard, trhs, extra))(using ctxs.withCond(negCaseConds))
      }
      rec(cases, Seq.empty)
    }

    final def unfoldArgs(args: Seq[Code], extra: Extra)(using env: Env, ctxs: Ctxs): (Seq[(T, CodeRes)], Ctxs) = {
      args.foldLeft((Seq.empty[(T, CodeRes)], ctxs)) {
        case ((acc, ctxs), arg) =>
          given Ctxs = ctxs
          assert(CodeRes.isTerminal(arg))
          val (tres, cr) = unfold(arg, extra)
          assert(cr.terminal == arg)
          (acc :+ (tres, cr), cr.ctxs)
      }
    }
  }

  final def tearDown(c: Code)(using env: Env, ctxs: Ctxs): CodeRes = {
    object tear extends CodeTransformer {
      override type Extra = Unit

      override def transformImpl(c: Code, repl: Map[Code, Code], extra: Extra)(using env: Env, ctxs: Ctxs): CodeRes = code2sig(c) match {
        case Signature(Label.Or, first +: rest) =>
          val firstTeared = transform(first, repl, ())
          val terminal = codeOfDisjs(firstTeared.terminal +: rest)
          firstTeared.derived(terminal)

        case Signature(Label.Not, Seq(cc)) =>
          val teared = transform(cc, repl, ())
          val terminal = codeOfSig(mkNot(teared.terminal), BoolTy)
          teared.derived(terminal)

        case Signature(Label.IfExpr, Seq(cond, thn, els)) =>
          val condTeared = transform(cond, repl, ())
          val terminal = codeOfSig(mkIfExpr(condTeared.terminal, thn, els), codeTpe(c))
          condTeared.derived(terminal)

        case Signature(_: (Label.Ensuring.type | Label.LambdaLike), _) => CodeRes(c, ctxs.addBoundDef(c))

        case MatchExprSig(scrut, cases) =>
          val scrutTeared = transform(scrut, repl, ())
          val terminal = codeOfSig(mkMatchExpr(scrutTeared.terminal, cases), codeTpe(c))
          scrutTeared.derived(terminal)

        case PassesSig(scrut, cases) =>
          val scrutTeared = transform(scrut, repl, ())
          val terminal = codeOfSig(mkPasses(scrutTeared.terminal, cases), codeTpe(c))
          scrutTeared.derived(terminal)

        case _ => super.transformImpl(c, repl, ())
      }
    }

    unplugged(c).map(_._1)
      .getOrElse(tear.transform(c, Map.empty, ()))
  }

  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Match expression utilities

  final def tupleSubscrutinees(scrut: Code, tt: TupleType): Seq[Code] = {
    tt.bases.zipWithIndex.map { case (base, i) => tupleSelect(scrut, i + 1, base) }
  }

  final def adtSubScrutinees(scrut: Code, adt: ADTType): Seq[Code] = {
    val tcons = getConstructor(adt.id, adt.tps)
    tcons.fields.map(fld => adtSelect(scrut, Label.ADTSelector(adt, tcons, fld.id), fld.getType))
  }

  final def adtMatchCond(scrut: Code, adt: ADTType)(using Env, Ctxs): Code = {
    isConstructor(scrut, adt, adt.id) match {
      case Some(true) => trueCode
      case Some(false) => falseCode
      case None => codeOfSig(mkIsCtor(scrut, adt, adt.id), BoolTy)
    }
  }

  case class UnapplySubScruts(unapplyInvoc: Code, getInvoc: Code, subs: Seq[Code], patCond: Code)

  final def unapplySubScrutinees(scrut: Code, id: Identifier, tps: Seq[Type]): UnapplySubScruts = {
    val fdUnapply = getFunction(id, tps)
    val unapplyInvocSig = mkFunInvoc(id, tps, Seq(scrut))
    val unapplyInvoc = codeOfSig(unapplyInvocSig, fdUnapply.returnType)

    // The accessor in question is either get or isEmpty so fnId = get or isEmpty
    // In short: get(unapplyInvoc) or isEmpty(unapplyInvoc) depending on what we pass as fnId
    // See Expression#UnapplyPattern
    def unapplyAccessor(fnId: Identifier): Code = {
      val fdAcc = getFunction(fnId)
      assert(fdAcc.params.size == 1)
      val tpMap = instantiation(fdAcc.params.head.tpe, fdUnapply.returnType)
        .getOrElse(sys.error("Unapply pattern failed type instantiation"))
      val typedFd = fdAcc.typed(fdAcc.typeArgs map tpMap)

      val accInvocSig = mkFunInvoc(typedFd.id, typedFd.tps, Seq(unapplyInvoc))
      codeOfSig(accInvocSig, typedFd.returnType)
    }

    val isUnapplyFlag = fdUnapply.flags.collectFirst {
      case f@IsUnapply(_, _) => f
    }.getOrElse(sys.error("Oh non, on nous a menti encore une fois :("))

    val getInvoc = unapplyAccessor(isUnapplyFlag.get)
    val isEmptyInvoc = unapplyAccessor(isUnapplyFlag.isEmpty)
    val nonEmpty = codeOfSig(mkNot(isEmptyInvoc), BoolTy)

    codeTpe(getInvoc) match {
      case tt@TupleType(_) =>
        val subs = tupleSubscrutinees(getInvoc, tt)
        UnapplySubScruts(unapplyInvoc, getInvoc, subs, nonEmpty)
      case _ =>
        // The subpattern is getInvoc itself, as we don't need to de-structure it into a tuple
        UnapplySubScruts(unapplyInvoc, getInvoc, Seq(getInvoc), nonEmpty)
    }
  }

  case class PatBdgsAndConds(ctxs: Ctxs, bdgs: Seq[Code], patConds: Seq[Code])

  final def addPatternBindingsAndConds(ctxs: Ctxs, scrut: Code, pat: LabelledPattern)(using env: Env): PatBdgsAndConds = {
    def recHelper(ctxs: Ctxs, subscruts: Seq[Code], subps: Seq[LabelledPattern]): PatBdgsAndConds = {
      assert(subscruts.size == subps.size)
      subscruts.zip(subps).foldLeft(PatBdgsAndConds(ctxs, Seq.empty[Code], Seq.empty[Code])) {
        case (PatBdgsAndConds(ctxs, bdgsAcc, condsAcc), (subscrut, subpat)) =>
          val PatBdgsAndConds(ctxs2, bdgs2, conds2) = addPatternBindingsAndConds(ctxs.addBoundDef(subscrut), subscrut, subpat)
          PatBdgsAndConds(ctxs2, bdgsAcc ++ bdgs2, condsAcc ++ conds2)
      }
    }

    assert(ctxs.isLitVarOrBoundDef(scrut))
    pat match {
      case LabelledPattern.Wildcard => PatBdgsAndConds(ctxs, Seq.empty, Seq.empty)
      case LabelledPattern.Lit(lit) =>
        val cond = codeOfSig(mkEquals(scrut, codeOfLit(lit)), BoolTy)
        PatBdgsAndConds(ctxs.withCond(cond), Seq.empty, Seq(cond))

      case LabelledPattern.ADT(id, tps, subps) =>
        val subscruts = adtSubScrutinees(scrut, ADTType(id, tps))
        val adtPatCond = adtMatchCond(scrut, ADTType(id, tps))(using env, ctxs)
        val PatBdgsAndConds(newCtxs, recBdgs, recPatConds) = recHelper(ctxs.withCond(adtPatCond), subscruts, subps)
        assert(ctxs.isPrefixOf(newCtxs))
        PatBdgsAndConds(newCtxs, subscruts ++ recBdgs, adtPatCond +: recPatConds)

      case LabelledPattern.TuplePattern(subps) =>
        val tt@TupleType(bases) = codeTpe(scrut): @unchecked
        assert(bases.size == subps.size)
        val subscruts = tupleSubscrutinees(scrut, tt)
        val PatBdgsAndConds(newCtxs, recBdgs, recPatConds) = recHelper(ctxs, subscruts, subps)
        assert(ctxs.isPrefixOf(newCtxs))
        PatBdgsAndConds(newCtxs, subscruts ++ recBdgs, recPatConds)

      case LabelledPattern.Unapply(recs, id, tps, subps) =>
        assert(recs.isEmpty)
        val unapp = unapplySubScrutinees(scrut, id, tps)
        // 1. We bind unapply(scrut): Option[...]
        // 2. We make sure the return Option is a Some (with unapp.patCond)
        // 3. We bind unapply(scrut).get
        val ctxs2 = ctxs.addBoundDef(unapp.unapplyInvoc)
          .withCond(unapp.patCond)
          .addBoundDef(unapp.getInvoc)
        val PatBdgsAndConds(newCtxs, recBdgs, recPatConds) = recHelper(ctxs2, unapp.subs, subps)
        assert(ctxs.isPrefixOf(newCtxs))

        val theseBdgs =
          if (unapp.subs == Seq(unapp.getInvoc)) Seq(unapp.patCond, unapp.getInvoc) // To avoid having 2x unapp.getInvoc in subs
          else Seq(unapp.patCond, unapp.getInvoc) ++ unapp.subs

        PatBdgsAndConds(newCtxs, theseBdgs ++ recBdgs, unapp.patCond +: recPatConds)
    }
  }

  //endregion

  /////////////////////////////////////////////////////////////////////////////////////////////////////////

  //region Misc

  object LitSig {
    def unapply(sig: Signature): Option[Literal[_]] = sig match {
      case Signature(Label.Lit(l), _) => Some(l)
      case _ => None
    }
  }

  object IntLikeLitSig {
    def unapply(sig: Signature): Option[BigInt] = sig match {
      case Signature(Label.Lit(bv@BVLiteral(_, _, _)), _) => Some(bv.toBigInt)
      case Signature(Label.Lit(IntegerLiteral(v)), _) => Some(v)
      case _ => None
    }
  }

  object IntLikeLitCode {
    def unapply(c: Code): Option[BigInt] = IntLikeLitSig.unapply(code2sig(c))
  }

  object PlusSig {
    def unapply(sig: Signature): Option[(Code, Code)] = sig match {
      case Signature(Label.Plus, Seq(a, b)) => Some((a, b))
      case _ => None
    }
  }

  object MinusSig {
    def unapply(sig: Signature): Option[(Code, Code)] = sig match {
      case Signature(Label.Minus, Seq(a, b)) => Some((a, b))
      case _ => None
    }
  }

  object OrSig {
    def unapply(sig: Signature): Option[(Seq[Code], Boolean)] = sig match {
      case Signature(Label.Or, disjs) => Some((disjs, true))
      case Signature(Label.Not, Seq(c)) => code2sig(c) match {
        case Signature(Label.Or, disjs) => Some((disjs, false))
        case _ => None
      }
      case _ => None
    }
  }

  object BoolLitSig {
    def unapply(sig: Signature): Option[Boolean] = sig match {
      case Signature(Label.Lit(BooleanLiteral(b)), _) => Some(b)
      case _ => None
    }
  }

  object EqSig {
    def unapply(sig: Signature): Option[(Code, Code)] = sig match {
      case Signature(Label.Equals, Seq(lhs, rhs)) => Some((lhs, rhs))
      case _ => None
    }
  }

  object EqCode {
    def unapply(c: Code): Option[(Code, Code)] = code2sig(c) match {
      case Signature(Label.Equals, Seq(lhs, rhs)) => Some((lhs, rhs))
      case _ => None
    }
  }

  object LeqSig {
    def unapply(sig: Signature): Option[(Code, Code)] = sig match {
      case Signature(Label.LessEquals, Seq(lhs, rhs)) => Some((lhs, rhs))
      case _ => None
    }
  }

  object LtSig {
    def unapply(sig: Signature): Option[(Code, Code)] = sig match {
      case Signature(Label.LessThan, Seq(lhs, rhs)) => Some((lhs, rhs))
      case _ => None
    }
  }

  object GeqSig {
    def unapply(sig: Signature): Option[(Code, Code)] = sig match {
      case Signature(Label.GreaterEquals, Seq(lhs, rhs)) => Some((lhs, rhs))
      case _ => None
    }
  }

  object GtSig {
    def unapply(sig: Signature): Option[(Code, Code)] = sig match {
      case Signature(Label.GreaterThan, Seq(lhs, rhs)) => Some((lhs, rhs))
      case _ => None
    }
  }

  object NotSig {
    def unapply(sig: Signature): Option[Code] = sig match {
      case Signature(Label.Not, Seq(c)) => Some(c)
      case _ => None
    }
  }

  object MatchExprSig {
    def unapply(sig: Signature): Option[(Code, Seq[LabMatchCase])] = sig match {
      case Signature(Label.MatchExpr(pats), scrut +: guardRhs) =>
        assert(2 * pats.size == guardRhs.size)
        assert(CodeRes.isTerminal(scrut))
        val cases = pats.zip(guardRhs.grouped(2)).map {
          case (pat, Seq(guard, rhs)) => LabMatchCase(pat, guard, rhs)
          case _ => sys.error("oh non, je ne sais pas compter :(")
        }
        Some((scrut, cases))
      case _ => None
    }
  }

  object PassesSig {
    def unapply(sig: Signature): Option[(Code, Seq[LabMatchCase])] = sig match {
      case Signature(Label.Passes(pats), scrut +: guardRhs) =>
        assert(2 * pats.size == guardRhs.size)
        assert(CodeRes.isTerminal(scrut))
        val cases = pats.zip(guardRhs.grouped(2)).map {
          case (pat, Seq(guard, rhs)) => LabMatchCase(pat, guard, rhs)
          case _ => sys.error("oh non, je ne sais pas compter :(")
        }
        Some((scrut, cases))
      case _ => None
    }
  }

  object ArraySelSig {
    def unapply(sig: Signature): Option[(Code, Code)] = sig match {
      case Signature(Label.ArraySelect, Seq(arr, i)) => Some((arr, i))
      case _ => None
    }
  }

  object ArraySelCode {
    def unapply(c: Code): Option[(Code, Code)] = code2sig(c) match {
      case Signature(Label.ArraySelect, Seq(arr, i)) => Some((arr, i))
      case _ => None
    }
  }

  object ArrayUpdCode {
    def unapply(c: Code): Option[(Code, Code, Code)] = code2sig(c) match {
      case Signature(Label.ArrayUpdated, Seq(arr, i, v)) => Some((arr, i, v))
      case _ => None
    }
  }

  final def isPrefixOf[T](lhs: Seq[T], rhs: Seq[T]): Boolean =
    lhs.size <= rhs.size && lhs.zip(rhs).forall { case (l, r) => l == r }

  final def findMap[A, B](as: Seq[A])(f: A => Option[B]): Option[B] =
    if (as.isEmpty) None
    else f(as.head).orElse(findMap(as.tail)(f))

  final def indexWhereOpt[A](as: Seq[A])(f: A => Boolean): Option[Int] = {
    val ix = as.indexWhere(f)
    if (ix < 0) None else Some(ix)
  }

  final def addIfAbsent[K, V](map: Map[K, V])(kv: (K, V)): Map[K, V] =
    if (map.contains(kv._1)) map else map + kv

  final def tryFoldLeft[E, A, T](as: Seq[A], init: T)(f: (T, A) => Either[E, T]): Either[E, T] = {
    def rec(as: Seq[A], acc: T): Either[E, T] = as match {
      case Seq() => Right(acc)
      case head +: tail => f(acc, head) match {
        case Left(e) => Left(e)
        case Right(newAcc) => rec(tail, newAcc)
      }
    }
    rec(as, init)
  }

  final def provablyNeq(c1: Code, c2: Code): Boolean = {
    def argsNeq(args1: Seq[Code], args2: Seq[Code]): Boolean =
      args1.size != args2.size || args1.zip(args2).exists(provablyNeq.tupled)

    (code2sig(c1), code2sig(c2)) match {
      case (LitSig(l1), LitSig(l2)) => l1 != l2
      case (Signature(Label.ADT(id1, tps1), args1), Signature(Label.ADT(id2, tps2), args2)) =>
        id1 != id2 || tps1 != tps2 || argsNeq(args1, args2)
      case (Signature(Label.FiniteArray(_), elems1), Signature(Label.FiniteArray(_), elems2)) =>
        argsNeq(elems1, elems2)
      case (Signature(Label.FiniteSet(_), elems1), Signature(Label.FiniteSet(_), elems2)) =>
        argsNeq(elems1, elems2)
      case _ => false
    }
  }

  // Is `c` an ADT with constructor `id`?
  //   Some(true) - Yes
  //   Some(false) - No
  //   None - Can't tell
  final def isConstructor(c: Code, adt: ADTType, id: Identifier)(using Env, Ctxs): Option[Boolean] = {
    def codeIsCtor(ofId: Identifier): Code =
      codeOfSig(Signature(Label.IsConstructor(adt, ofId), Seq(c)), BoolTy)

    def codeNotCtor(ofId: Identifier): Code =
      negCodeOf(codeIsCtor(ofId))

    code2sig(c) match {
      case Signature(Label.ADT(id2, _), _) => Some(id == id2)
      case _ =>
        if (implied(codeIsCtor(id))) Some(true)
        else if (implied(codeNotCtor(id))) Some(false)
        else {
          val cons = getConstructor(id, adt.tps)
          val sort = cons.sort
          // All other constructors (excluding `id`) for the ADT
          val alts = (sort.constructors.toSet - cons).map(_.id)

          if (alts.exists(alt => implied(codeIsCtor(alt)))) Some(false)
          else if (alts.forall(alt => implied(codeNotCtor(alt)))) Some(true)
          else None
        }
    }
  }

  final def idOfVariable(v: Variable): VarId = var2VarId.get(v) match {
    case Some(vId) => vId
    case None =>
      val vId = VarId.fromInt(varIdCounter)
      varIdCounter += 1
      var2VarId += v -> vId
      varId2Var += vId -> v
      vId
  }

  final def code2sig(c: Code): Signature = code2sigMap(c)

  final def codeTpe(c: Code): Type = codeTpeMap(c)

  final def freshened(v: VarId): VarId = idOfVariable(varId2Var(v).freshen)

  final def freshVarId(name: String, tpe: Type): VarId = idOfVariable(Variable.fresh(name, tpe))

  final def codeOfSig(sig: Signature, tpe: Type): Code = {
    sig2codeMap.get(sig) match {
      case Some(c) =>
        assert(codeTpeMap(c) == tpe, s"${codeTpeMap(c)} != $tpe")
        c
      case None =>
        val newCode = Code.fromInt(sig2codeMap.size)
        assert(!code2sigMap.contains(newCode))
        sig2codeMap += sig -> newCode
        code2sigMap += newCode -> sig
        codeTpeMap += newCode -> tpe
        newCode
    }
  }

  final def label(c: Code): Label = code2sig(c).label

  final def varTpe(v: VarId): Type = varId2Var(v).getType

  final def codeOfDisjs(d: Seq[Code]): Code = {
    assert(d.nonEmpty)
    if (d.size == 1) d.head else codeOfSig(mkOr(d), BoolTy)
  }

  final def codeOfIntLit(lit: BigInt, tpe: Type): Code = codeOfLit(intLitOfType(lit, tpe))

  final def intLitOfType(lit: BigInt, tpe: Type): Literal[_] = tpe match {
    case IntegerType() => IntegerLiteral(lit)
    case RealType() => FractionLiteral(lit, 1)
    case bvt@BVType(signed, size) =>
      assert(fits(lit, bvt))
      BVLiteral(signed, lit, size)
    case _ => sys.error(s"$tpe is not an integer-like type")
  }

  final def fits(lit: BigInt, bvt: BVType): Boolean = {
    if (bvt.signed && lit < 0) false
    else {
      val (loIncl, hiExcl) = {
        if (bvt.signed) (-BigInt(2).pow(bvt.size - 1), BigInt(2).pow(bvt.size - 1))
        else (BigInt(0), BigInt(2).pow(bvt.size))
      }
      loIncl <= lit && lit < hiExcl
    }
  }

  final def codeOfVarId(v: VarId): Code = codeOfSig(mkVar(v), varTpe(v))

  final def codeOfLit[T](l: Literal[T]): Code = codeOfSig(mkLit(l), l.getType)

  final def isLambda(c: Code): Boolean = code2sig(c).label.isLambda

  final def isLambdaLike(c: Code): Boolean = code2sig(c).label.isLambdaLike

  final def isVar(c: Code): Boolean = code2sig(c).label.isVar

  final def isLit(c: Code): Boolean = code2sig(c).label.isLiteral

  final def isLitOrVar(c: Code): Boolean = code2sig(c).label.isLitOrVar

  final def b2c(b: Boolean): Code = if (b) trueCode else falseCode

  final def b2sig(b: Boolean): Signature = if (b) trueSig else falseSig

  final val assmChkPurity: Purity = if (opts.assumeChecked) Pure else Impure

  final def unAnd(e: Expr): Seq[Expr] = e match {
    case And(es) => es.flatMap(unAnd)
    case SplitAnd(es) => es.flatMap(unAnd)
    case Not(Not(e)) => unAnd(e)
    case e => Seq(e)
  }

  final def unOr(e: Expr): Seq[Expr] = e match {
    case Or(es) => es.flatMap(unOr)
    case Not(Not(e)) => unOr(e)
    case Implies(e1, e2) => unOr(Not(e1)) ++ unOr(e2)
    case e => Seq(e)
  }

  final def unOrCodes(disjs: Seq[Code]): Seq[Code] = disjs.flatMap(unOrCode)

  final def unOrCode(c: Code): Seq[Code] = code2sig(c) match {
    case Signature(Label.Or, disjs) => disjs.flatMap(unOrCode)
    case _ => Seq(c)
  }

  // Map all codes to their corresponding signatures (for debugging purposes)

  case class ExplicitSig(label: Label, children: Seq[ExplicitSig]) {
    override def toString: String = {
      if (children.isEmpty) label.toString
      else s"($label, ${children.mkString(", ")})"
    }
  }

  final def asExplicitSig(c: Code): ExplicitSig = {
    val sig = code2sig(c)
    ExplicitSig(sig.label, sig.children.map(asExplicitSig))
  }
  //endregion
}
