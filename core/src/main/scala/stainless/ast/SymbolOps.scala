/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package ast

import scala.collection.mutable.{Map => MutableMap}

trait SymbolOps extends inox.ast.SymbolOps { self: TypeOps =>
  import trees._
  import trees.exprOps._
  import symbols._

  override protected def createSimplifier(popts: inox.solvers.PurityOptions): SimplifierWithPC = new {
    val opts: inox.solvers.PurityOptions = popts
  } with transformers.SimplifierWithPC with SimplifierWithPC

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

      case ADTPattern(ob, id, tps, subps) =>
        val tcons = getConstructor(id, tps)
        assert(tcons.fields.size == subps.size)
        val pairs = tcons.fields zip subps
        val subTests = pairs.map(p => apply(adtSelector(in, p._1.id), p._2))
        pp.empty withCond isCons(in, id) merge bind(ob, in) merge subTests

      case TuplePattern(ob, subps) =>
        val TupleType(tpes) = in.getType
        assert(tpes.size == subps.size)
        val subTests = subps.zipWithIndex.map { case (p, i) => apply(tupleSelect(in, i+1, subps.size), p) }
        bind(ob, in) merge subTests

      case up @ UnapplyPattern(ob, _, _, _, subps) =>
        val subs = unwrapTuple(up.get(in), subps.size).zip(subps) map (apply _).tupled
        bind(ob, in) withCond Not(up.isEmpty(in)) merge subs

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
    def bindIn(vd: Option[ValDef]): Map[ValDef,Expr] = vd match {
      case None => Map()
      case Some(vd) => Map(vd -> in)
    }

    pattern match {
      case ADTPattern(b, id, tps, subps) =>
        val tcons = getConstructor(id, tps)
        assert(tcons.fields.size == subps.size)
        val pairs = tcons.fields zip subps
        val subMaps = pairs.map(p => mapForPattern(adtSelector(in, p._1.id), p._2))
        val together = subMaps.flatten.toMap
        bindIn(b) ++ together

      case TuplePattern(b, subps) =>
        val TupleType(tpes) = in.getType
        assert(tpes.size == subps.size)

        val maps = subps.zipWithIndex.map { case (p, i) => mapForPattern(tupleSelect(in, i+1, subps.size), p)}
        val map = maps.flatten.toMap
        bindIn(b) ++ map

      case up @ UnapplyPattern(b, _, _, _, subps) =>
        bindIn(b) ++ unwrapTuple(up.get(in), subps.size).zip(subps).flatMap {
          case (e, p) => mapForPattern(e, p)
        }.toMap

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
}
