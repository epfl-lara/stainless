/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package ast

/* @nv: necessary to ensure the self-type bound of SymbolOps can be satisfied
 *      while at the same time having {{{val trees: stainless.ast.Trees}}} */
trait TypeOps extends inox.ast.TypeOps {
  protected val trees: Trees
}

trait SymbolOps extends inox.ast.SymbolOps { self: TypeOps =>
  import trees._
  import trees.exprOps._
  import symbols._

  /**
   * Get the source of this function
   *
   * i.e. either its identifier or the identifier of its (recursively) outer function.
   *
   * NOTE no need to actually recurse here as [[Derived]] already
   *      holds the requested data.
   */
  def source(fd: FunDef): Identifier =
    fd.flags collectFirst { case Derived(id) => id } getOrElse fd.id

  override protected def createSimplifier(opts: inox.solvers.PurityOptions) =
    new SimplifierWithPC(opts) with transformers.SimplifierWithPC

  override protected def createTransformer[P <: PathLike[P]](path: P, f: (Expr, P, TransformerOp[P]) => Expr)
                                                            (implicit ppP: PathProvider[P]): TransformerWithPC[P] =
    new TransformerWithPC[P](path, f) with transformers.TransformerWithPC with TransformerWithFun {
      val pp = ppP
    }

  override def isImpureExpr(expr: Expr): Boolean = expr match {
    case (_: Require) | (_: Ensuring) | (_: Assert) => true
    case _ => super.isImpureExpr(expr)
  }

  /** Extracts path conditions from patterns and scrutinees, @see [[conditionForPattern]] */
  protected class PatternConditions[P <: PathLike[P]](includeBinders: Boolean)(implicit pp: PathProvider[P]) {
    protected final def bind(ob: Option[ValDef], to: Expr): P = {
      if (!includeBinders) {
        pp.empty
      } else {
        ob.map(vd => pp.empty withBinding (vd -> to)).getOrElse(pp.empty)
      }
    }

    def apply(in: Expr, pattern: Pattern): P = pattern match {
      case WildcardPattern(ob) =>
        bind(ob, in)

      case InstanceOfPattern(ob, adt) =>
        val tadt = adt.asInstanceOf[ADTType].getADT
        if (tadt.root == tadt) {
          bind(ob, in)
        } else {
          pp.empty withCond isInstOf(in, adt) merge bind(ob, in)
        }

      case ADTPattern(ob, adt, subps) =>
        val tcons = adt.getADT.toConstructor
        assert(tcons.fields.size == subps.size)
        val pairs = tcons.fields zip subps
        val subTests = pairs.map(p => apply(adtSelector(asInstOf(in, adt), p._1.id), p._2))
        pp.empty withCond isInstOf(in, adt) merge bind(ob, asInstOf(in, adt)) merge subTests

      case TuplePattern(ob, subps) =>
        val TupleType(tpes) = in.getType
        assert(tpes.size == subps.size)
        val subTests = subps.zipWithIndex.map { case (p, i) => apply(tupleSelect(in, i+1, subps.size), p) }
        bind(ob, in) merge subTests

      case up @ UnapplyPattern(ob, id, tps, subps) =>
        val subs = unwrapTuple(up.get(in), subps.size).zip(subps) map (apply _).tupled
        bind(ob, in) withCond up.isSome(in) merge subs

      case LiteralPattern(ob, lit) =>
        pp.empty withCond Equals(in, lit) merge bind(ob, in)
    }
  }

  /* Override point for extracting pattern conditions. */
  protected def patternConditions[P <: PathLike[P]](includeBinders: Boolean)(implicit pp: PathProvider[P]) =
    new PatternConditions[P](includeBinders)

  /** Recursively transforms a pattern on a boolean formula expressing the conditions for the input expression, possibly including name binders
    *
    * For example, the following pattern on the input `i`
    * {{{
    * case m @ MyCaseClass(t: B, (_, 7)) =>
    * }}}
    * will yield the following condition before simplification (to give some flavour)
    *
    * {{{and(IsInstanceOf(MyCaseClass, i), and(Equals(m, i), InstanceOfClass(B, i.t), equals(i.k.arity, 2), equals(i.k._2, 7))) }}}
    *
    * Pretty-printed, this would be:
    * {{{
    * i.instanceOf[MyCaseClass] && m == i && i.t.instanceOf[B] && i.k.instanceOf[Tuple2] && i.k._2 == 7
    * }}}
    *
    * @see [[purescala.Expressions.Pattern]]
    */
  final def conditionForPattern[P <: PathLike[P]]
                               (in: Expr, pattern: Pattern, includeBinders: Boolean = false)
                               (implicit pp: PathProvider[P]): P = patternConditions(includeBinders)(pp)(in, pattern)

  /** Converts the pattern applied to an input to a map between identifiers and expressions */
  def mapForPattern(in: Expr, pattern: Pattern): Map[ValDef,Expr] = {
    def bindIn(vd: Option[ValDef], cast: Option[ADTType] = None): Map[ValDef,Expr] = vd match {
      case None => Map()
      case Some(vd) => Map(vd -> cast.map(asInstOf(in, _)).getOrElse(in))
    }

    pattern match {
      case ADTPattern(b, adt, subps) =>
        val tcons = adt.getADT.toConstructor
        assert(tcons.fields.size == subps.size)
        val pairs = tcons.fields zip subps
        val subMaps = pairs.map(p => mapForPattern(adtSelector(asInstOf(in, adt), p._1.id), p._2))
        val together = subMaps.flatten.toMap
        bindIn(b, Some(adt)) ++ together

      case TuplePattern(b, subps) =>
        val TupleType(tpes) = in.getType
        assert(tpes.size == subps.size)

        val maps = subps.zipWithIndex.map { case (p, i) => mapForPattern(tupleSelect(in, i+1, subps.size), p)}
        val map = maps.flatten.toMap
        bindIn(b) ++ map

      case up @ UnapplyPattern(b, _, _, subps) =>
        bindIn(b) ++ unwrapTuple(up.getUnsafe(in), subps.size).zip(subps).flatMap {
          case (e, p) => mapForPattern(e, p)
        }.toMap

      case InstanceOfPattern(b, adt: ADTType) =>
        bindIn(b, Some(adt))

      case other =>
        bindIn(other.binder)
    }
  }

  /** Rewrites all pattern-matching expressions into if-then-else expressions
    * Introduces additional error conditions. Does not introduce additional variables.
    */
  def matchToIfThenElse(expr: Expr, assumeExhaustive: Boolean = true): Expr = {

    def rewritePM(e: Expr): Option[Expr] = e match {
      case m @ MatchExpr(scrut, cases) =>
        val condsAndRhs = for (cse <- cases) yield {
          val map = mapForPattern(scrut, cse.pattern)
          val patCond = conditionForPattern[Path](scrut, cse.pattern, includeBinders = false)
          val realCond = cse.optGuard match {
            case Some(g) => patCond withCond replaceFromSymbols(map, g)
            case None => patCond
          }
          val newRhs = replaceFromSymbols(map, cse.rhs)
          (realCond.toClause, newRhs, cse)
        }

        val (branches, elze) = if (assumeExhaustive) {
          val (cases :+ ((_, rhs, _))) = condsAndRhs
          (cases, rhs)
        } else {
          (condsAndRhs, Error(m.getType, "Match is non-exhaustive").copiedFrom(m))
        }

        val bigIte = branches.foldRight(elze)((p1, ex) => {
          if(p1._1 == BooleanLiteral(true)) {
            p1._2
          } else {
            IfExpr(p1._1, p1._2, ex).copiedFrom(p1._3)
          }
        })

        Some(bigIte)

      case _ => None
    }

    preMap(rewritePM)(expr)
  }

  /** For each case in the [[purescala.Expressions.MatchExpr MatchExpr]],
   *  concatenates the path condition with the newly induced conditions.
   *
   *  Each case holds the conditions on other previous cases as negative.
   *
    * @see [[purescala.ExprOps#conditionForPattern conditionForPattern]]
    * @see [[purescala.ExprOps#mapForPattern mapForPattern]]
    */
  def matchExprCaseConditions[P <: PathLike[P] : PathProvider](m: MatchExpr, path: P) : Seq[P] = {
    val MatchExpr(scrut, cases) = m
    var pcSoFar = path

    for (c <- cases) yield {
      val g = c.optGuard getOrElse BooleanLiteral(true)
      val cond = conditionForPattern[P](scrut, c.pattern, includeBinders = true)
      val localCond = pcSoFar merge (cond withCond g)

      // These contain no binders defined in this MatchCase
      val condSafe = conditionForPattern[P](scrut, c.pattern)
      val gSafe = replaceFromSymbols(mapForPattern(scrut, c.pattern), g)
      pcSoFar = pcSoFar merge (condSafe withCond gSafe).negate

      localCond
    }
  }

  /** Condition to pass this match case, expressed w.r.t scrut only */
  def matchCaseCondition[P <: PathLike[P] : PathProvider](scrut: Expr, c: MatchCase): P = {

    val patternC = conditionForPattern[P](scrut, c.pattern, includeBinders = false)

    c.optGuard match {
      case Some(g) =>
        // guard might refer to binders
        val map  = mapForPattern(scrut, c.pattern)
        patternC withCond replaceFromSymbols(map, g)

      case None =>
        patternC
    }
  }


  /* ======================
   * Stainless Constructors
   * ====================== */

  def tupleWrapArg(fun: Expr) = fun.getType match {
    case FunctionType(args, res) if args.size > 1 =>
      val newArgs = fun match {
        case Lambda(args, _) => args
        case _ => args map (tpe => ValDef(FreshIdentifier("x", true), tpe))
      }

      val res = ValDef(FreshIdentifier("res", true), TupleType(args))
      val patt = TuplePattern(None, newArgs map (arg => WildcardPattern(Some(arg))))
      Lambda(Seq(res), MatchExpr(res.toVariable, Seq(
        MatchCase(patt, None, application(fun, newArgs map (_.toVariable)))
      ))).copiedFrom(fun)

    case _ => fun
  }

  def assertion(c: Expr, err: Option[String], res: Expr) = {
    if (c == BooleanLiteral(true)) {
      res
    } else if (c == BooleanLiteral(false)) {
      Error(res.getType, err.getOrElse("Assertion failed"))
    } else {
      Assert(c, err, res)
    }
  }

  def req(pred: Expr, body: Expr) = pred match {
    case BooleanLiteral(true)  => body
    case BooleanLiteral(false) => Error(body.getType, "Precondition failed")
    case _ => Require(pred, body)
  }

  def ensur(e: Expr, pred: Expr) = {
    Ensuring(e, tupleWrapArg(pred).asInstanceOf[Lambda]).setPos(e)
  }

  def funRequires(f: Expr, p: Expr) = {
    val FunctionType(from, to) = f.getType
    assert(from.nonEmpty, "Can't build `requires` for function without arguments")
    val vds = from.map(tpe => ValDef(FreshIdentifier("x", true), tpe))
    val vars = vds.map(_.toVariable)
    Forall(vds, 
      Implies(
        Application(p, vars).copiedFrom(f), 
        Application(Pre(f).copiedFrom(f), vars).copiedFrom(f)
      ).copiedFrom(f)
    ).copiedFrom(f)
  }

  def funEnsures(f: Expr, p: Expr) = {
    val FunctionType(from, to) = f.getType
    assert(from.nonEmpty, "Can't build `ensures` for function without arguments")
    val vds = from.map(tpe => ValDef(FreshIdentifier("x", true), tpe).setPos(tpe))
    val vars = vds.map(_.toVariable)
    Forall(vds, 
      Implies(
        Application(Pre(f).copiedFrom(f), vars).copiedFrom(f), 
        Application(p, vars :+ Application(f, vars).copiedFrom(f)).copiedFrom(f)
      ).copiedFrom(f)
    ).copiedFrom(f)
  }

  /* =================
   * Path manipulation
   * ================= */

  /** Merges the given [[Path]] into the provided [[Expressions.Expr]].
    *
    * This method expects to run on a [[Definitions.FunDef.fullBody]] and merges into
    * existing pre- and postconditions.
    *
    * @param expr The current body
    * @param path The path that should be wrapped around the given body
    * @see [[Expressions.Ensuring]]
    * @see [[Expressions.Require]]
    */
  def withPath(expr: Expr, path: Path): Expr = {
    def unwrap(e: Expr): Lambda = e match {
      case Let(i, e, b) =>
        val Lambda(args, body) = unwrap(b)
        Lambda(args, let(i, e, body)).copiedFrom(e)
      case l: Lambda => l
      case _ => scala.sys.error("Should never happen!")
    }

    def spec(cond: Expr, es: Seq[Expr]): Expr = es match {
      case Seq(e) => req(cond, e)
      case Seq(e, pre) => req(and(cond, pre), e)
      case Seq(e, pre, post) => ensur(req(and(cond, pre), e), unwrap(post))
      case _ => scala.sys.error("Should never happen!")
    }

    expr match {
      case Let(i, e, b) => withPath(b, path withBinding (i -> e))
      case Require(pre, b) => path withShared (Seq(b, pre), spec)
      case Ensuring(Require(pre, b), post) => path withShared (Seq(b, pre, post), spec)
      case Ensuring(b, post) => path withShared (Seq(b, BooleanLiteral(true), post), spec)
      case b => path withShared (Seq(b), spec)
    }
  }


  /* ====================
   * Weakest precondition
   * ==================== */

  /**
   * [[strict]] enable the strict arithmetic mode. See [[AssertionInjector.optStrictkArithmetic]].
   * Overload with context below.
   */
  def weakestPrecondition(e: Expr, strict: Boolean): Expr = {
    object injector extends verification.AssertionInjector {
      val s: trees.type = trees
      val t: trees.type = trees
      val symbols: self.symbols.type = self.symbols
      val strictArithmetic: Boolean = strict
    }

    val withAssertions = injector.transform(e)

    var results: List[Expr] = Nil
    object collector extends transformers.TransformerWithPC {
      val trees: self.trees.type = self.trees
      val symbols: self.symbols.type = self.symbols

      val pp = Path
      val initEnv = Path.empty
      type Env = Path

      override protected def rec(e: Expr, path: Path): Expr = e match {
        case _: Lambda =>
          e
        case _: Require =>
          accumulate(e, path)
          e
        case _ =>
          val res = super.rec(e, path)
          accumulate(e, path)
          res
      }

      protected def accumulate(e: Expr, path: Path): Unit = e match {
        case Assert(pred, _, _) => results :+= path implies pred
        case Require(pred, _) => results :+= path implies pred

        case fi @ FunctionInvocation(_, _, args) =>
          val pred = replaceFromSymbols(fi.tfd.paramSubst(args), fi.tfd.precOrTrue)
          results :+= path implies pred

        case Application(caller, args) =>
          results :+= path implies Application(Pre(caller).copiedFrom(caller), args).copiedFrom(e)

        case _ =>
      }
    }

    collector.transform(withAssertions)
    andJoin(results)
  }

  def weakestPrecondition(e: Expr)(implicit ctx: inox.Context): Expr =
    weakestPrecondition(e, ctx.options.findOptionOrDefault(verification.optStrictArithmetic))
}
