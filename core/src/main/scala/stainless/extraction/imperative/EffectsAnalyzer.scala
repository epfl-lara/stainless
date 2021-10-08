/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction
package imperative

import inox.FatalError

/** Provides effect analysis for full Stainless language
  *
  * This holds state for caching the current state of the analysis, so if
  * you modify your program you may want to create a new EffectsAnalysis
  * instance.
  *
  * You can use it lazily by only querying effects for the functions you need.
  * The internals make sure to compute only the part of the dependencies graph
  * that is needed to get the effect of the function.
  *
  * An effect is defined as the impact that a function can have on its environment.
  * In the Stainless language, there are no global variables that aren't explicit, so
  * the effect of a function is defined as the set of its parameters that are mutated
  * by executing the body. It is a conservative over-abstraction, as some update operations
  * might actually not modify the object, but this will still be considered as an
  * effect.
  *
  * There are actually a very limited number of features that rely on global state (epsilon).
  * EffectsAnalysis will not take such effects into account. You need to make sure the
  * program either does not rely on epsilon, or has been rewriting with the IntroduceGlobalStatePhase
  * phase that introduce any global state explicitly as function parameters. In the future,
  * if we do end up supporting global variables, it is likely that we will rely on another
  * phase to introduce that global state explicitly into the list of parameters of functions
  * that make use of it.
  *
  * An effect is detected by a FieldAssignment to one of the parameters that are mutable. It
  * can come from transitively calling a function that perform a field assignment as well.
  * If the function uses higher-order functions that take mutable types as parameters, they
  * will be conservatively assumed to perform an effect as well. A function type is not by itself
  * a mutable type, but if it is applied on a mutable type that is taken as a parameter as well,
  * it will be detected as an effect by the EffectsAnalysis.
  * TODO: maybe we could have "conditional effects", effects depending on the effects of the lambda.
  *
  * The EffectsAnalysis also provides functions to analyze the the mutability of a type and expression.
  * The isMutableType function needs to perform a graph traversal (explore all the fields recursively
  * to find if one is mutable)
  *
  * Throughout the code, we assume that there is no aliasing. This is the global assumption made
  * in Stainless for effects. Some alias analysis to check that property needs to be performed before
  * relying on the EffectsAnalysis features.
  * TODO: we might integrate the limited alias analysis for pattern matching with substitution inside here
  *       Or better, we should introduce a simple AliasAnalysis class that provide functionalities.
  */
trait EffectsAnalyzer extends oo.CachingPhase {
  val s: Trees
  val t: s.type
  import s._
  import exprOps._
  import context.given

  private[this] val effectsCache = new ExtractionCache[FunDef, Result]((fd, context) =>
    getDependencyKey(fd.id)(using context.symbols)
  )

  protected case class Result(
    effects: Map[FunAbstraction, Set[Effect]],
    locals: Map[Identifier, FunAbstraction]) {

    def merge(that: Result): Result = Result(effects ++ that.effects, locals ++ that.locals)

    def asString(using PrinterOptions): String = {
      val effectsString = effects.map(e => "  " + e._1.id.asString + " -> " + e._2.map(_.asString)).toList.sorted.mkString("\n")
      val localsString = locals.map(p => "  " + p._1.asString + "," + p._2.asString).toList.sorted.mkString("\n")
      s"""|effects:
          |$effectsString
          |
          |locals:
          |$localsString""".stripMargin
    }
  }

  protected object Result {
    def empty: Result = Result(Map.empty, Map.empty)
  }

  protected type TransformerContext <: EffectsAnalysis

  trait EffectsAnalysis { self: TransformerContext =>
    val symbols: s.Symbols
    import symbols.given

    private[this] def functionEffects(fd: FunAbstraction, current: Result): Set[Effect] =
      BodyWithSpecs(fd.fullBody).bodyOpt match {
        case Some(body) =>
          expressionEffects(body, current)
        case None if !fd.flags.contains(IsPure) =>
          fd.params
            .filter(vd => symbols.isMutableType(vd.getType) && !vd.flags.contains(IsPure))
            .map(_.toVariable)
            .map(ModifyingEffect(_, Path(Seq.empty)))
            .toSet
        case _ =>
          Set.empty
      }

    private[this] val result: Result = symbols.functions.values.foldLeft(Result.empty) {
      case (results, fd) =>
        val fds = (symbols.transitiveCallees(fd) + fd).toSeq.sortBy(_.id)
        val lookups = fds.map(effectsCache get (_, this))
        val newFds = (fds zip lookups).filter(_._2.isEmpty).map(_._1)
        val prevResult = lookups.flatten.foldLeft(Result.empty)(_ merge _)

        val newResult = if (newFds.isEmpty) {
          prevResult
        } else {
          val inners = newFds.map { fd =>
            fd -> collect[FunAbstraction] {
              case LetRec(fds, _) => fds.map(Inner(_)).toSet
              case _ => Set.empty
            } (fd.fullBody)
          }.toMap

          val baseResult = Result(
            inners.flatMap { case (fd, inners) => inners + Outer(fd) }.map(_ -> Set.empty[Effect]).toMap,
            inners.flatMap { case (_, inners) => inners.map(fun => fun.id -> fun) })

          val result = inox.utils.fixpoint[Result] { case res @ Result(effects, locals) =>
            Result(effects.map { case (fd, _) => fd -> functionEffects(fd, res) }, locals)
          } (prevResult merge baseResult)

          for ((fd, inners) <- inners) {
            effectsCache(fd, this) = Result(
              result.effects.filter { case (fun, _) => fun == Outer(fd) || inners(fun) },
              result.locals.filter { case (_, fun) => inners(fun) }
            )
          }

          result
        }

        results merge newResult
    }

    def effects(fd: FunDef): Set[Effect] = result.effects(Outer(fd))
    def effects(fun: FunAbstraction): Set[Effect] = result.effects(fun)
    def effects(expr: Expr): Set[Effect] = expressionEffects(expr, result)

    private[imperative] def local(id: Identifier): FunAbstraction = result.locals(id)

    private[imperative] def getAliasedParams(fd: FunAbstraction): Seq[ValDef] = {
      val receivers = effects(fd).map(_.receiver)
      fd.params.filter(vd => receivers(vd.toVariable))
    }

    private[imperative] def getReturnType(fd: FunAbstraction): Type = {
      val aliasedParams = getAliasedParams(fd)
      tupleTypeWrap(fd.returnType +: aliasedParams.map(_.tpe))
    }

    def asString(using PrinterOptions): String =
      s"EffectsAnalysis(\n${result.asString}\n)"

    override def toString: String = asString
  }

  sealed abstract class Accessor {
    def asString(using inox.Context): String
    def bind(x: ValDef, e: Expr): Accessor
  }

  case class ADTFieldAccessor(selector: Identifier) extends Accessor {
    def asString(using inox.Context) = s"ADTFieldAccessor(${selector.asString})"
    def bind(x: ValDef, e: Expr): Accessor = this
  }

  case class ClassFieldAccessor(selector: Identifier) extends Accessor {
    def asString(using inox.Context) = s"ClassFieldAccessor(${selector.asString})"
    def bind(x: ValDef, e: Expr): Accessor = this
  }

  case class ArrayAccessor(index: Expr) extends Accessor {
    def asString(using inox.Context) = s"ArrayAccessor(${index.asString})"
    def bind(x: ValDef, e: Expr): Accessor = ArrayAccessor(bindNonValue(x, e, index))
  }

  case object UnknownArrayAccessor extends Accessor {
    def asString(using inox.Context) = s"UnknownArrayAccessor"
    def bind(x: ValDef, e: Expr): Accessor = this
  }

  case class MutableMapAccessor(index: Expr) extends Accessor {
    def asString(using inox.Context) = s"MutableMapAccessor(${index.asString})"
    def bind(x: ValDef, e: Expr): Accessor = MutableMapAccessor(bindNonValue(x, e, index))
  }

  case class TupleFieldAccessor(index: Int) extends Accessor {
    def asString(using inox.Context) = s"TupleFieldAccessor($index)"
    def bind(x: ValDef, e: Expr): Accessor = this
  }

  case class Path(path: Seq[Accessor]) {
    def :+(elem: Accessor): Path = Path(path :+ elem)
    def +:(elem: Accessor): Path = Path(elem +: path)
    def ++(that: Path): Path = Path(this.path ++ that.path)
    def length: Int = path.length

    def isEmpty: Boolean = path.isEmpty

    def wrap(expr: Expr)(using Symbols) = Path.wrap(expr, path)

    def bind(x: ValDef, e: Expr) = Path(path.map(_.bind(x, e)))

    // can return `true` even if `this` is not really a prefix of `that`
    // (because of array and mutable map accessors)
    def maybePrefixOf(that: Path): Boolean = {
      // TODO: more expressions can be added to be "provably different"
      def provablyDifferent(index1: Expr, index2: Expr): Boolean = (index1, index2) match {
        case (x1: Variable, Plus(x2: Variable, BVLiteral(_, _, size)))
          if x1 == x2 && x1.tpe == BVType(true, 32) && size <= 32 => true
        case (Plus(x2: Variable, BVLiteral(_, _, size)), x1: Variable)
          if x1 == x2 && x1.tpe == BVType(true, 32) && size <= 32 => true
        case (BVLiteral(signed1, value1, size1), BVLiteral(signed2, value2, size2))
          if value1 != value2 => true
        case _ => false
      }

      def rec(p1: Seq[Accessor], p2: Seq[Accessor]): Boolean = (p1, p2) match {
        case (Seq(), _) => true
        case (ArrayAccessor(index1) +: xs1, ArrayAccessor(index2) +: xs2) if !provablyDifferent(index1, index2) =>
          rec(xs1, xs2)
        case (ADTFieldAccessor(id1) +: xs1, ADTFieldAccessor(id2) +: xs2) if id1 == id2 =>
          rec(xs1, xs2)
        case (ClassFieldAccessor(id1) +: xs1, ClassFieldAccessor(id2) +: xs2) if id1 == id2 =>
          rec(xs1, xs2)
        case (TupleFieldAccessor(id1) +: xs1, TupleFieldAccessor(id2) +: xs2) if id1 == id2 =>
          rec(xs1, xs2)
        case (MutableMapAccessor(_) +: xs1, MutableMapAccessor(_) +: xs2) =>
          rec(xs1, xs2)
        case _ => false
      }

      rec(path, that.path)
    }

    // can return `false` even if `this` is a prefix of `that`
    def definitelyPrefixOf(that: Path): Boolean = {
      def rec(p1: Seq[Accessor], p2: Seq[Accessor]): Boolean = (p1, p2) match {
        case (Seq(), _) => true
        case (ArrayAccessor(index1) +: xs1, ArrayAccessor(index2) +: xs2) if index1 == index2 =>
          rec(xs1, xs2)
        case (ADTFieldAccessor(id1) +: xs1, ADTFieldAccessor(id2) +: xs2) if id1 == id2 =>
          rec(xs1, xs2)
        case (ClassFieldAccessor(id1) +: xs1, ClassFieldAccessor(id2) +: xs2) if id1 == id2 =>
          rec(xs1, xs2)
        case (TupleFieldAccessor(id1) +: xs1, TupleFieldAccessor(id2) +: xs2) if id1 == id2 =>
          rec(xs1, xs2)
        case (MutableMapAccessor(k1) +: xs1, MutableMapAccessor(k2) +: xs2) if k1 == k2 =>
          rec(xs1, xs2)
        case _ => false
      }

      rec(path, that.path)
    }

    def toSeq: Seq[Accessor] = path

    def asString(using PrinterOptions): String =
      path.map {
        case ADTFieldAccessor(id) => s".${id.asString}"
        case ClassFieldAccessor(id) => s".${id.asString}"
        case TupleFieldAccessor(idx) => s"._$idx"
        case ArrayAccessor(idx) => s"(${idx.asString})"
        case UnknownArrayAccessor => s"(???)"
        case MutableMapAccessor(idx) => s"(${idx.asString})"
      }.mkString("")

    override def toString: String = asString
  }

  object Path {
    def empty: Path = Path(Seq.empty)

    def wrap(expr: Expr, path: Seq[Accessor])(using symbols: Symbols): Option[Expr] = path match {
      case ADTFieldAccessor(id) +: xs =>
        wrap(ADTSelector(expr, id), xs)

      case TupleFieldAccessor(idx) +: xs =>
        wrap(TupleSelect(expr, idx), xs)

      case ClassFieldAccessor(id) +: xs =>
        def asClassType(tpe: Type): Option[ClassType] = tpe match {
          case ct: ClassType => Some(ct)
          case ta: TypeApply if !ta.isAbstract => asClassType(ta.resolve)
          case other => None
        }

        for {
          ct  <- asClassType(expr.getType)
          tcd <- symbols.classForField(ct, id)
          res <- if (tcd.cd.parents.isEmpty && tcd.cd.children.isEmpty)
            wrap(ClassSelector(expr, id), xs)
          else
            wrap(ClassSelector(AsInstanceOf(expr, tcd.toType), id), xs)
        } yield res

      case ArrayAccessor(idx) +: xs =>
        wrap(ArraySelect(expr, idx), xs)

      case MutableMapAccessor(idx) +: xs =>
        wrap(MutableMapApply(expr, idx), xs)

      case Seq() =>
        Some(expr)
    }

  }

  // values that do not need binding
  private def isValue(e: Expr): Boolean = e match {
    case _: Variable => true
    case UnitLiteral() => true
    case BooleanLiteral(_) => true
    case IntegerLiteral(_) => true
    case BVLiteral(_, _, _) => true
    case Tuple(es) => es.forall(isValue)
    case ADT(_, _, args) => args.forall(isValue)
    case _ => false
  }

  def bindNonValue(x: ValDef, e: Expr, body: Expr): Expr = {
    if (isValue(e)) exprOps.replaceFromSymbols(Map(x -> e), body)
    else if (exprOps.variablesOf(body).contains(x.toVariable)) Let(x, e, body)
    else body
  }

  case class Target(receiver: Variable, condition: Option[Expr], path: Path) {
    def +(elem: Accessor): Target = Target(receiver, condition, path :+ elem)

    def bind(x: ValDef, e: Expr) = Target(receiver, condition.map(cond => bindNonValue(x, e, cond)), path.bind(x, e))

    def append(that: Target): Target = (condition, that.condition) match {
      case (condition, None) =>
        Target(receiver, condition, path ++ that.path)
      case (None, _) =>
        Target(receiver, that.condition, path ++ that.path)
      case (Some(condition), Some(thatCondition)) =>
        Target(receiver, Some(And(condition, thatCondition)), path ++ that.path)
    }

    def prependPath(path: Path): Target = Target(receiver, condition, path ++ this.path)
    def appendPath(path: Path): Target = Target(receiver, condition, this.path ++ path)

    def toEffect(effectKind: EffectKind): Effect = effectKind match {
      case ReplacementKind => ReplacementEffect(receiver, path)
      case ModifyingKind => ModifyingEffect(receiver, path)
      case CombinedKind => CombinedEffect(receiver, path)
    }

    def maybePrefixOf(that: Target): Boolean =
      receiver == that.receiver && (path maybePrefixOf that.path)

    def definitelyPrefixOf(that: Target): Boolean =
      receiver == that.receiver && (path definitelyPrefixOf that.path)

    def wrap(using Symbols): Option[Expr] = path.wrap(receiver)

    def asString(using PrinterOptions): String =
      s"Target(${receiver.asString}, ${condition.map(_.asString)}, ${path.asString})"

    override def toString: String = asString

    def isValid(using syms: Symbols): Boolean = {
      def rec(tpe: Type, path: Seq[Accessor]): Boolean = (tpe, path) match {
        case (adt: ADTType, ADTFieldAccessor(id) +: xs) =>
          val constructors = adt.getSort.constructors
          val constructor = constructors.find(_.fields.exists(_.id == id))
          val field = constructor.flatMap(_.fields.find(_.id == id))
          field.isDefined && rec(field.get.getType, xs)

        case (ct: ClassType, ClassFieldAccessor(id) +: xs) =>
          val field = syms.classForField(ct, id).flatMap(_.fields.find(_.id == id))
          field.isDefined && rec(field.get.getType, xs)

        case (tt: TupleType, TupleFieldAccessor(idx) +: xs) =>
          0 < idx && idx <= tt.dimension && rec(tt.bases(idx - 1), xs)

        case (ArrayType(base), ArrayAccessor(idx) +: xs) =>
          rec(base, xs)

        case (_, Nil) =>
          true
      }

      rec(receiver.getType, path.toSeq)
    }
  }


  /* We consider three kinds of effects:
   * - replacement effects, which assign `receiver.path` to an expression
   * - modifying effects (`replacement == false`), which make a modification deeper (e.g. `receiver.path.x = e`)
   * - combined effects, combining replacement and modifying effects
   */
  sealed abstract class EffectKind
  case object ReplacementKind extends EffectKind
  case object ModifyingKind extends EffectKind
  case object CombinedKind extends EffectKind

  object Effect {
    def apply(kind: EffectKind, receiver: Variable, path: Path): Effect = kind match {
      case ReplacementKind => ReplacementEffect(receiver, path)
      case ModifyingKind => ModifyingEffect(receiver, path)
      case CombinedKind => CombinedEffect(receiver, path)
    }
  }

  sealed abstract class Effect(val kind: EffectKind) {
    val receiver: Variable
    val path: Path

    def +(elem: Accessor): Effect = Effect(kind, receiver, path :+ elem)
    def ++(path2: Path): Effect = Effect(kind, receiver, path ++ path2)
    def precise(elem: Accessor) = ReplacementEffect(receiver, path :+ elem)

    def withPath(newPath: Path): Effect = Effect(kind, receiver, newPath)
    def withKind(newKind: EffectKind): Effect = Effect(newKind, receiver, path)

    def removeUnknownAccessor: Effect = {
      val newPath = Path(path.path.takeWhile(_ != UnknownArrayAccessor))
      val newKind = if (kind == ReplacementKind) ModifyingKind else kind
      if (path != newPath) Effect(newKind, receiver, newPath)
      else this
    }

    def on(that: Expr)(using symbols: Symbols): Set[Effect] = {
      val res = try {
        getTargets(that, kind, path.path).map(_.toEffect(kind))
      } catch {
        case _: MalformedStainlessCode => throw MalformedStainlessCode(that,
          s"Couldn't apply effect ${this.asString} on expression ${that.asString}"
        )
      }
      for (e <- res if e.kind == CombinedKind && e.path.isEmpty && !this.path.isEmpty) {
        context.reporter.fatalError(that.getPos,
          s"Ambiguous effect ${this.asString} on ${that.asString}"
        )
      }
      res
    }

    def maybePrefixOf(that: Effect): Boolean =
      receiver == that.receiver && (path maybePrefixOf that.path)

    def definitelyPrefixOf(that: Effect): Boolean =
      receiver == that.receiver && (path definitelyPrefixOf that.path)

    def toTarget: Target = Target(receiver, None, path)

    def wrap(using Symbols): Option[Expr] = path.wrap(receiver)

    def targetString(using PrinterOptions): String =
      s"${receiver.asString}${path.asString}"

    def asString(using PrinterOptions): String

    override def toString: String = asString
  }

  case class ReplacementEffect(receiver: Variable, path: Path) extends Effect(ReplacementKind) {
    def asString(using PrinterOptions) = s"ReplacementEffect($targetString)"
  }

  case class ModifyingEffect(receiver: Variable, path: Path) extends Effect(ModifyingKind) {
    def asString(using PrinterOptions) = s"ModifyingEffect($targetString)"
  }

  case class CombinedEffect(receiver: Variable, path: Path) extends Effect(CombinedKind) {
    def asString(using PrinterOptions) = s"CombinedEffect($targetString)"
  }


  /* getTargets(expr, Seq()) returns the set of targets (receiver/path) such that after `var x = expr`,
   * effects (with `kind`) on `x` (field assignments, array updates, etc.) result in effects on
   * these targets.
   */
  def getTargets(expr: Expr, kind: EffectKind, path: Seq[Accessor] = Seq.empty)(using symbols: Symbols): Set[Target] = expr match {
    case _ if variablesOf(expr).forall(v => !symbols.isMutableType(v.tpe)) => Set.empty
    case _ if isExpressionFresh(expr) => Set.empty
    case _ if !symbols.isMutableType(expr.getType) => Set.empty
    case _ if kind == ReplacementKind && path.isEmpty => Set.empty

    case v: Variable => Set(Target(v, None, Path(path)))
    case ADTSelector(e, id) => getTargets(e, kind, ADTFieldAccessor(id) +: path)
    case ClassSelector(e, id) => getTargets(e, kind, ClassFieldAccessor(id) +: path)
    case TupleSelect(e, idx) => getTargets(e, kind, TupleFieldAccessor(idx) +: path)
    case ArraySelect(a, idx) => getTargets(a, kind, ArrayAccessor(idx) +: path)
    case MutableMapApply(a, idx) => getTargets(a, kind, MutableMapAccessor(idx) +: path)
    case MutableMapDuplicate(m) => getTargets(m, kind, path)

    case ADT(id, _, args) => path match {
      case ADTFieldAccessor(fid) +: rest =>
        getTargets(args(symbols.getConstructor(id).fields.indexWhere(_.id == fid)), kind, rest)
      case _ =>
        if (kind != ReplacementKind)
          throw MalformedStainlessCode(expr, s"Couldn't compute effect targets in ADT ${expr.asString}")
        else Set.empty
    }

    case ClassConstructor(ct, args) => path match {
      case ClassFieldAccessor(fid) +: rest =>
        getTargets(args(ct.tcd.fields.indexWhere(_.id == fid)), kind, rest)
      case _ =>
        if (kind != ReplacementKind)
          throw MalformedStainlessCode(expr, s"Couldn't compute effect targets in class constructor ${expr.asString}")
        else Set.empty
    }

    case Tuple(exprs) => path match {
      case TupleFieldAccessor(idx) +: rest =>
        getTargets(exprs(idx - 1), kind, rest)
      case _ =>
        if (kind != ReplacementKind)
          throw MalformedStainlessCode(expr, s"Couldn't compute effect targets in tuple ${expr.asString}")
        else Set.empty
    }

    case FiniteArray(elems, _) => path match {
      case ArrayAccessor(bv: BVLiteral) +: rest =>
        val i = bv.toBigInt.toInt
        if (i < elems.size) getTargets(elems(i), kind, rest)
        else throw MalformedStainlessCode(expr, s"Out of bound array access in ${expr.asString}")
      case Seq(UnknownArrayAccessor) if kind == ReplacementKind =>
        Set.empty
      case _ if kind == ReplacementKind && path.isEmpty =>
        Set.empty
      case _ if kind == ReplacementKind && !path.head.isInstanceOf[ArrayAccessor] && path.head != UnknownArrayAccessor =>
        Set.empty
      case _ =>
        throw MalformedStainlessCode(expr, s"Couldn't compute effect targets in finite array ${expr.asString}")
    }

    case Assert(_, _, e) => getTargets(e, kind, path)
    case Annotated(e, _) => getTargets(e, kind, path)

    case m: MatchExpr =>
      getTargets(symbols.matchToIfThenElse(m), kind, path)

    case IfExpr(cnd, thn, els) =>
      def notConj(cnd: Expr, e: Option[Expr])(): Expr = e map { e =>
        And(Not(cnd).setPos(cnd), e.setPos(cnd)).setPos(cnd)
      } getOrElse(Not(cnd).setPos(cnd))

      def conj(cnd: Expr, e: Option[Expr])(): Expr = e map { e =>
        And(cnd, e.setPos(cnd)).setPos(cnd)
      } getOrElse(cnd)

      getTargets(thn, kind, path).map { t =>
        Target(t.receiver, Some(conj(cnd, t.condition)()),  t.path)
      }.filter(_.isValid) ++
      getTargets(els, kind, path).map { t =>
        Target(t.receiver, Some(notConj(cnd, t.condition)()),  t.path)
      }.filter(_.isValid)

    case fi: FunctionInvocation if !symbols.isRecursive(fi.id) =>
      val specced = BodyWithSpecs(symbols.simplifyLets(fi.inlined))
      specced.bodyOpt
        .map(specced.wrapLets)
        .map(getTargets(_, kind, path))
        .getOrElse(Set.empty)

    case fi: FunctionInvocation => Set.empty
    case (_: ApplyLetRec | _: Application) => Set.empty
    case _: LargeArray | _: ArrayUpdated if kind == ReplacementKind && path.isEmpty =>
      Set.empty
    case _: LargeArray | _: ArrayUpdated if kind == ReplacementKind && !path.head.isInstanceOf[ArrayAccessor] && path.head != UnknownArrayAccessor =>
      Set.empty
    case _: MutableMapUpdated => Set.empty
    case _: ArrayUpdated => Set.empty
    case IsInstanceOf(e, _) => getTargets(e, kind, path)
    case AsInstanceOf(e, _) => getTargets(e, kind, path)
    case Old(_) => Set.empty
    case Snapshot(_) => Set.empty
    case FreshCopy(_) => Set.empty

    case ArrayLength(_) => Set.empty

    case FiniteSet(elements, tpe) => Set.empty
    case SetUnion(s1, s2) => Set.empty
    case SetIntersection(s1, s2) => Set.empty
    case SetDifference(s1, s2) => Set.empty
    case SubsetOf(s1, s2) => Set.empty
    case ElementOfSet(element, set) => Set.empty
    case SetAdd(bag, element) => Set.empty

    case FiniteBag(elements, tpe) => Set.empty
    case BagUnion(s1, s2) => Set.empty
    case BagIntersection(s1, s2) => Set.empty
    case BagDifference(s1, s2) => Set.empty
    case MultiplicityInBag(element, bag) => Set.empty
    case BagAdd(bag, element) => Set.empty

    case Block(_, last) => getTargets(last, kind, path)

    case Let(vd, e, b) if !symbols.isMutableType(vd.tpe) =>
      getTargets(b, kind, path).map(_.bind(vd, e))

    case Let(vd, e, b) =>
      getTargets(b, kind, path).map(_.bind(vd, e)).flatMap { be =>
        if (be.receiver == vd.toVariable) getTargets(e, kind, be.path.path)
        else Set(be)
      }

    case _ =>
      throw MalformedStainlessCode(expr,
        s"Couldn't compute effect targets in (${expr.getClass}): ${expr.asString}\n" +
        s"Path: ${path.map(_.asString)}"
      )
  }

  def getAllTargets(expr: Expr)(using Symbols) = getTargets(expr, ModifyingKind)
  def getDirectTargets(expr: Expr, accessor: Accessor)(using Symbols) =
    getTargets(expr, ReplacementKind, Seq(accessor))

  /* A fresh expression is an expression that is newly created
   * and does not share memory with existing values and variables.
   *
   * If the expression is made of existing immutable variables (Int or
   * immutable case classes), it is considered fresh as we consider all
   * non mutable objects to have a value-copy semantics.
   *
   * It turns out that an expression of non-mutable type is always fresh,
   * as it can not contain references to a mutable object, by definition
   */
  def isExpressionFresh(expr: Expr)(using symbols: Symbols): Boolean = {
    import symbols._

    def rec(expr: Expr, bindings: Set[ValDef]): Boolean = !isMutableType(expr.getType) || (expr match {
      case v: Variable => bindings(v.toVal)
      case ADT(_, _, args) => args.forall(rec(_, bindings))

      case FiniteArray(elems, _) => elems.forall(rec(_, bindings))
      case LargeArray(elems, default, _, _) => elems.forall(p => rec(p._2, bindings)) && rec(default, bindings)

      // We assume `old(.)` is fresh here, although such cases will probably be
      // rejected later in `ImperativeCleanup`.
      case Old(_) => true

      case fi @ FunctionInvocation(id, _, _) if !symbols.isRecursive(id) =>
        BodyWithSpecs(symbols.simplifyLets(fi.inlined))
          .bodyOpt
          .forall(isExpressionFresh)

      // other function invocations always return a fresh expression, by hypothesis (global assumption)
      case (_: FunctionInvocation | _: ApplyLetRec | _: Application) => true

      // ArrayUpdated returns a mutable array, which by definition is a clone of the original
      case ArrayUpdated(IsTyped(_, ArrayType(base)), _, _) => !isMutableType(base)

      // MutableMapDuplicate returns a fresh duplicate by definition
      case MutableMapDuplicate(IsTyped(_, MutableMapType(from, to))) =>
        !isMutableType(from) && !isMutableType(to)

      // snapshots & fresh copies are fresh
      case Snapshot(_) => true
      case FreshCopy(_) => true

      // For `Let`, it is safe to add `vd` as a fresh binding because we disallow
      // `FieldAssignments` with non-fresh expressions in `EffetsChecker.check(fd: FunAbstraction)`.
      // See discussion on: https://github.com/epfl-lara/stainless/pull/985#discussion_r614583479
      case Let(vd, e, b) => rec(e, bindings) && rec(b, bindings + vd)

      // A `LetVar` can be fresh if `vd` is only assigned fresh values both
      // here and in all subsequent Assign statements.
      case LetVar(vd, expr, b) if rec(expr, bindings) && !exprOps.exists {
        case Assignment(v, e) if v.toVal == vd => !rec(e, bindings + vd)
        case _ => false
      }(b) =>
        rec(b, bindings + vd)

      // Otherwise, we don't add `vd` as a fresh binding, because it might be reassigned
      // to a non-fresh expression in a `Block` appearing in `b` (see link above)
      case LetVar(vd, _, b) => rec(b, bindings)

      case Block(_, e) => rec(e, bindings)

      case IfExpr(_, e1, e2) => rec(e1, bindings) && rec(e2, bindings)
      case MatchExpr(_, cases) => cases.forall(cse => rec(cse.rhs, bindings))

      //any other expression is conservatively assumed to be non-fresh if
      //any sub-expression is non-fresh
      case Operator(args, _) => args.forall(rec(_, bindings))
    })

    rec(expr, Set.empty)
  }

  protected def typeToAccessor(tpe: Type, id: Identifier)(using Symbols): Accessor = tpe match {
    case at: ADTType   => ADTFieldAccessor(id)
    case ct: ClassType => ClassFieldAccessor(id)
    case ta: TypeApply => typeToAccessor(ta.getType, id)
    case _ => throw FatalError(s"Cannot have accessors over type $tpe")
  }

  /** Return all effects of expr
    *
    * Effects of expr are any free variables in scope (either local vars
    * already defined in the scope containing expr, or global var) that
    * are re-assigned by an operation in the expression. An effect is
    * also a mutation of an object referred by an id defined in the scope.
    *
    * This is a conservative analysis, not taking into account control-flow.
    * The set of effects is not definitely effects, but any identifier
    * not in the set will for sure have no effect.
    *
    * We are assuming no aliasing.
    */
  private def expressionEffects(expr: Expr, result: Result)(using symbols: Symbols): Set[Effect] = {
    import symbols._
    val freeVars = variablesOf(expr).filter(vd => isMutableType(vd.tpe) || vd.flags.contains(IsVar))

    def inEnv(effect: Effect, env: Map[Variable, Effect]): Option[Effect] =
      env.get(effect.receiver).map(e => Effect(effect.kind, e.receiver, e.path ++ effect.path))

    def effect(expr: Expr, env: Map[Variable, Effect]): Set[Effect] =
      getAllTargets(expr) flatMap { (target: Target) =>
        inEnv(target.toEffect(ModifyingKind), env).toSet
      }

    def rec(expr: Expr, env: Map[Variable, Effect]): Set[Effect] = expr match {
      case Let(vd, e, b) if symbols.isMutableType(vd.tpe) =>

        if ((variablesOf(e) & variablesOf(b)).forall(v => !isMutableType(v.tpe))) {
          val effe = rec(e, env)
          val newEnv = (variablesOf(b) ++ freeVars).map(v => v -> ModifyingEffect(v, Path.empty)).toMap
          val effb = rec(b, newEnv)
          effe ++ effb.flatMap { ef =>
            if (ef.receiver == vd.toVariable) ef.on(e)
            else Set(ef)
          }.flatMap(inEnv(_, env))
        }
        else
          rec(e, env) ++ rec(b, env ++ effect(e, env).map(vd.toVariable -> _))

      case MatchExpr(scrut, cses) if symbols.isMutableType(scrut.getType) =>
        rec(scrut, env) ++ cses.flatMap { case MatchCase(pattern, guard, rhs) =>
          val newEnv = env ++ mapForPattern(scrut, pattern).flatMap {
            case (v, e) => effect(e, env).map(v.toVariable -> _)
          }
          guard.toSeq.flatMap(rec(_, newEnv)).toSet ++ rec(rhs, newEnv)
        }

      case Swap(array1, index1, array2, index2) =>
        rec(array1, env) ++ rec(index1, env) ++ rec(array2, env) ++ rec(index2, env) ++
        effect(array1, env).map(_.precise(ArrayAccessor(index1))) ++
        effect(array2, env).map(_.precise(ArrayAccessor(index2)))

      case ArrayUpdate(o, idx, v) =>
        rec(o, env) ++ rec(idx, env) ++ rec(v, env) ++
        effect(o, env).map(_.precise(ArrayAccessor(idx)))

      case MutableMapUpdate(map, key, value) =>
        rec(map, env) ++ rec(key, env) ++ rec(value, env) ++
        effect(map, env).map(_.precise(MutableMapAccessor(key)))

      case MutableMapUpdated(map, key, value) =>
        rec(map, env) ++ rec(key, env) ++ rec(value, env)

      case ArrayUpdated(arr, key, value) =>
        rec(arr, env) ++ rec(key, env) ++ rec(value, env)

      case MutableMapDuplicate(map) =>
        rec(map, env)

      case fa @ FieldAssignment(o, id, v) =>
        val accessor = typeToAccessor(o.getType, id)
        rec(o, env) ++ rec(v, env) ++ effect(o, env).map(_.precise(accessor))

      case Application(callee, args) =>
        val ft @ FunctionType(_, _) = callee.getType
        val effects = functionTypeEffects(ft)
        rec(callee, env) ++ args.flatMap(rec(_, env)) ++
        args.map(effect(_, env)).zipWithIndex
          .filter(p => effects contains p._2)
          .flatMap(_._1)

      case Assignment(v, value) => rec(value, env) ++ env.get(v)

      case IfExpr(cnd, thn, els) =>
        rec(cnd, env) ++ rec(thn, env) ++ rec(els, env)

      case fi @ FunInvocation(id, tps, args, _) =>
        val fun = fi match {
          case FunctionInvocation(id, _, _) => Outer(getFunction(id))
          case ApplyLetRec(id, _, _, _, _) => result.locals(id)
        }

        if (fun.flags.contains(IsPure)) Set()
        else {
          val currentEffects: Set[Effect] = result.effects(fun)
          val paramSubst = (fun.params.map(_.toVariable) zip args).toMap
          val invocEffects = currentEffects.flatMap(e => paramSubst.get(e.receiver) match {
            case Some(arg) => (e on arg).flatMap(inEnv(_, env))
            case None => Seq(e) // This effect occurs on some variable captured from scope
          })

          val effectsOnLocalFreeVars = currentEffects.filterNot(e => paramSubst contains e.receiver)

          invocEffects ++ effectsOnLocalFreeVars ++ args.flatMap(rec(_, env))
        }

      case Operator(es, _) => es.flatMap(rec(_, env)).toSet
    }

    // We truncate the effects path if it goes through an inductive ADT as
    // such effects can lead to inexistence of the effects fixpoint.
    def truncate(effect: Effect): Effect = {
      def isInductive(tpe: Type, seen: Set[Identifier]): Boolean = {
        val deps = s.typeOps.collect {
          case ADTType(id, _) => dependencies(id)
          case ClassType(id, _) => dependencies(id)
          case _ => Set.empty[Identifier]
        } (tpe)

        (seen & deps).nonEmpty
      }

      def rec(tpe: Type, path: Seq[Accessor], seen: Set[Identifier]): Seq[Accessor] = (tpe, path) match {
        case (adt: ADTType, (fa @ ADTFieldAccessor(id)) +: xs) =>
          val field = adt.getSort.constructors.flatMap(_.fields).find(_.id == id).get
          if (isInductive(field.getType, seen)) Seq()
          else fa +: rec(field.getType, xs, seen + adt.id)
        case (ct: ClassType, (fa @ ClassFieldAccessor(id)) +: xs) =>
          val field = getClassField(ct, id).get
          if (isInductive(field.getType, seen)) Seq()
          else fa +: rec(field.getType, xs, seen + ct.id)
        case (tup: TupleType, (fa @ TupleFieldAccessor(idx)) +: xs) =>
          fa +: rec(tup.bases(idx - 1), xs, seen)
        case (ArrayType(base), (aa @ ArrayAccessor(i)) +: xs) =>
          val accessor = if (exprOps.variablesOf(i).isEmpty && expressionEffects(i, result).isEmpty) aa
                         else UnknownArrayAccessor
          accessor +: rec(base, xs, seen)
        case (ArrayType(base), UnknownArrayAccessor +: xs) =>
          UnknownArrayAccessor +: rec(base, xs, seen)
        case _ => Seq()
      }

      val newPath = Path(rec(effect.receiver.getType, effect.path.toSeq, Set()))
      val newKind =
        if (effect.path.length == newPath.length || effect.kind == CombinedKind) effect.kind
        else ModifyingKind

      effect.withPath(newPath).withKind(newKind)
    }

    val mutated = try (rec(expr, freeVars.map(v => v -> ModifyingEffect(v, Path.empty)).toMap))
      catch {
        case _: MalformedStainlessCode =>
          freeVars.map(v => ModifyingEffect(v, Path.empty)).toSet
      }

    val truncatedEffects = mutated.map(truncate)

    /* In `combinedEffects`:
     * - we drop effects for which there is a strictly shorter (prefix) effect (regardless of effect kind)
     * - two effects of different kinds with the same receiver/path become a combined effect
     * - a replacement effect which is strict prefix of other effects becomes a combined effect
     *     e.g. two replacement effects `x.a` and `x.a.b` become a combined effect on `x.a`
     *     this is consistent with the previous point, since a replacement effect `x.a.b` can be
     *     approximated by a modifying effect on `x.a`
     * - a modifying effect which is strict prefix of other effects remains a modifying effect
     *     e.g. a modifying effect on `x.a` and a replacement effect on `x.a.b` are equivalent to
     *     simply a modifying effect on `x.a`.
     * - a combined effect effect which is strict prefix of other effects remains a combined effect
     */
    val combinedEffects = truncatedEffects.flatMap { e =>
      if (truncatedEffects.exists(e2 => e.path != e2.path && e2.definitelyPrefixOf(e)))
        None // drop effects for which there is a strictly shorter (prefix) effect (regardless of effect kind)
      else if (truncatedEffects.exists(e2 => e.receiver == e2.receiver && e.path == e2.path && e.kind != e2.kind))
        Some(e.withKind(CombinedKind)) // different effects with the same receiver/path become combined effects
      else if (truncatedEffects.exists(e2 => e.definitelyPrefixOf(e2) && e.path != e2.path && e.kind == ReplacementKind))
        Some(e.withKind(CombinedKind)) // a top-level replacement, strict prefix of another effect, becomes a combined effect
      else
        Some(e)
    }

    combinedEffects
  }

  /** Effects at the level of types for a function
    *
    * This disregards the actual implementation of a function, and considers only
    * its type to determine a conservative abstraction of its effects.
    *
    * In theory this can be overridden to use a different behaviour.
    */
  def functionTypeEffects(ft: FunctionType)(using symbols: Symbols): Set[Int] = {
    ft.from.zipWithIndex.flatMap { case (tpe, i) =>
      if (symbols.isMutableType(tpe)) Some(i) else None
    }.toSet
  }
}
