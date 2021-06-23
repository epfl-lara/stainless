/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package ast

import inox.utils.Position
import inox.transformers.{TransformerOp, TransformerWithExprOp, TransformerWithTypeOp}

trait SymbolOps extends inox.ast.SymbolOps { self: TypeOps =>
  import trees._
  import trees.exprOps._
  import symbols._

  override protected def simplifierWithPC(popts: inox.solvers.PurityOptions): SimplifierWithPC = new {
    val opts: inox.solvers.PurityOptions = popts
  } with transformers.SimplifierWithPC with SimplifierWithPC with inox.transformers.SimplifierWithPath {
    override val pp = implicitly[PathProvider[Env]]
  }

  protected class TransformerWithPC[P <: PathLike[P]](
    initEnv: P,
    exprOp: (Expr, P, TransformerOp[Expr, P, Expr]) => Expr,
    typeOp: (Type, P, TransformerOp[Type, P, Type]) => Type
  )(implicit val pp: PathProvider[P]) extends super.TransformerWithPC[P](initEnv, exprOp, typeOp) {
    self0: TransformerWithExprOp with TransformerWithTypeOp =>
      val symbols = self.symbols
  }

  override protected def transformerWithPC[P <: PathLike[P]](
    path: P,
    exprOp: (Expr, P, TransformerOp[Expr, P, Expr]) => Expr,
    typeOp: (Type, P, TransformerOp[Type, P, Type]) => Type
  )(implicit pp: PathProvider[P]): TransformerWithPC[P] = {
    new TransformerWithPC[P](path, exprOp, typeOp)
      with transformers.TransformerWithPC
      with TransformerWithExprOp
      with TransformerWithTypeOp
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
        val subTests = pairs.map(p => apply(Annotated(adtSelector(in, p._1.id), Seq(Unchecked)), p._2))
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
        val subMaps = pairs.map(p => mapForPattern(Annotated(adtSelector(in, p._1.id), Seq(Unchecked)), p._2))
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
          (condsAndRhs, Error(m.getType, "match exhaustiveness").copiedFrom(m))
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

  /** Rewrites the given `max(e1, e2, ...)` into if-then-else expressions.
    */
  def maxToIfThenElse(max: Max): Expr = {
    require(max.exprs.nonEmpty)
    def go(exprs: Seq[Expr]): Expr = exprs match {
      case e1 :: Nil      => e1
      case e1 :: e2 :: es => IfExpr(GreaterThan(e1, e2).copiedFrom(max), e1, go(e2 :: es)).copiedFrom(max)
    }

    go(max.exprs)
  }

  /** Make a String representation for a table of Symbols `s`, only keeping
    * functions and classes whose names appear in `objs`.
    *
    * @see [[extraction.DebugPipeline]]
    */
  def debugString(filter: String => Boolean = (x: String) => true)(implicit pOpts: PrinterOptions): String = {
    wrapWith("Functions", objectsToString(functions.values, filter)) ++
    wrapWith("Sorts", objectsToString(sorts.values, filter))
  }

  protected def objectsToString(m: Iterable[Definition], filter: String => Boolean)
                               (implicit pOpts: PrinterOptions): String = {
    m.collect { case d if filter(d.id.name) => d.asString(pOpts) } mkString "\n\n"
  }

  protected def wrapWith(header: String, s: String) = {
    if (s.isEmpty) ""
    else "-------------" + header + "-------------\n" + s + "\n\n"
  }

  def paramInits(id: Identifier): Seq[FunDef] = {
    symbols.functions.values.toSeq.filter {
      case fd => fd.flags.exists {
        case ClassParamInit(cid) => id == cid
        case _ => false
      }
    }.sortBy(_.id.name.stripPrefix("apply$default$").toInt)
  }

}
