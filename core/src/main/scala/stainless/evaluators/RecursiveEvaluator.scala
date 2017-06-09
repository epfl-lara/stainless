/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package evaluators

trait RecursiveEvaluator extends inox.evaluators.RecursiveEvaluator {
  val program: Program
  import program._
  import program.trees._
  import program.symbols._

  override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Expr = expr match {
    case Require(pred, body) =>
      if (!ignoreContracts && e(pred) != BooleanLiteral(true))
        throw RuntimeError("Requirement did not hold @" + expr.getPos)
      e(body)

    case en @ Ensuring(body, pred) =>
      e(en.toAssert)

    case Assert(pred, err, body) =>
      if (!ignoreContracts && e(pred) != BooleanLiteral(true))
        throw RuntimeError(err.getOrElse("Assertion failed @" + expr.getPos))
      e(body)

    case Pre(f) =>
      e(f) match {
        case Lambda(args, body) => e(Lambda(args, weakestPrecondition(body)))
        case e => throw EvalError("Cannot get pre of non-lambda function " + e.asString)
      }

    case MatchExpr(scrut, cases) =>
      val rscrut = e(scrut)
      cases.toStream.map(c => matchesCase(rscrut, c).map(c -> _)).find(_.nonEmpty) match {
        case Some(Some((c, mapping))) => e(c.rhs)(rctx.withNewVars(mapping), gctx)
        case _ => throw RuntimeError("MatchError: " + rscrut + " did not match any of the cases:\n" + cases)
      }

    case FiniteArray(elems, base) =>
      FiniteArray(elems.map(e), base)

    case LargeArray(elems, default, size, base) =>
      LargeArray(elems.map(p => p._1 -> e(p._2)), e(default), e(size), base)

    case ArraySelect(array, index) => (e(array), e(index)) match {
      case (FiniteArray(elems, base), Int32Literal(i)) =>
        if (i < 0 || i >= elems.size) throw RuntimeError("Index out of bounds @" + expr.getPos)
        elems(i)
      case (LargeArray(elems, default, Int32Literal(size), _), Int32Literal(i)) =>
        if (i < 0 || i >= size) throw RuntimeError("Index out of bounds @" + expr.getPos)
        elems.get(i).getOrElse(default)
    }

    case ArrayUpdated(array, index, value) => (e(array), e(index)) match {
      case (FiniteArray(elems, base), Int32Literal(i)) =>
        if (i < 0 || i >= elems.size) throw RuntimeError("Index out of bounds @" + expr.getPos)
        FiniteArray(elems.updated(i, e(value)), base)
      case (LargeArray(elems, default, s @ Int32Literal(size), base), Int32Literal(i)) =>
        if (i < 0 || i >= size) throw RuntimeError("Index out of bounds @" + expr.getPos)
        LargeArray(elems + (i -> e(value)), default, s, base)
    }

    case ArrayLength(array) => e(array) match {
      case FiniteArray(elems, _) => Int32Literal(elems.size)
      case LargeArray(_, _, s, _) => s
    }

    case Error(tpe, msg) =>
      throw RuntimeError("Error reached in evaluation: " + msg)

    case NoTree(tpe) =>
      throw RuntimeError("Reached empty tree in evaluation @" + expr.getPos)

    case _ => super.e(expr)
  }

  protected def matchesCase(scrut: Expr, caze: MatchCase)
                           (implicit rctx: RC, gctx: GC): Option[Map[ValDef, Expr]] = {

    def obind(ob: Option[ValDef], e: Expr): Map[ValDef, Expr] = {
      Map.empty[ValDef, Expr] ++ ob.map(_ -> e)
    }

    def matchesPattern(pat: Pattern, expr: Expr): Option[Map[ValDef, Expr]] = (pat, expr) match {
      case (InstanceOfPattern(ob, pct), e) =>
        if (isSubtypeOf(e.getType, pct)) Some(obind(ob, e))
        else None

      case (WildcardPattern(ob), e) =>
        Some(obind(ob, e))

      case (ADTPattern(ob, tpe, subs), ADT(adt, args)) =>
        if (tpe == adt) {
          val res = (subs zip args) map (p => matchesPattern(p._1, p._2))
          if (res.forall(_.isDefined)) {
            Some(obind(ob, expr) ++ res.flatten.flatten)
          } else {
            None
          }
        } else {
          None
        }

      case (TuplePattern(ob, subs), Tuple(args)) =>
        if (subs.size == args.size) {
          val res = (subs zip args) map (p => matchesPattern(p._1, p._2))
          if (res.forall(_.isDefined)) {
            Some(obind(ob, expr) ++ res.flatten.flatten)
          } else {
            None
          }
        } else {
          None
        }

      case (up @ UnapplyPattern(ob, id, tps, subs), scrut) =>
        e(FunctionInvocation(id, tps, Seq(scrut))) match {
          case ADT(adt, Seq()) if adt == up.noneType => None
          case ADT(adt, Seq(arg)) if adt == up.someType =>
            val res = (subs zip unwrapTuple(arg, subs.size)) map (p => matchesPattern(p._1, p._2))
            if (res.forall(_.isDefined)) {
              Some(obind(ob, expr) ++ res.flatten.flatten)
            } else {
              None
            }
          case other => throw EvalError(typeErrorMsg(other, up.tfd.returnType))
        }

      case (LiteralPattern(ob, lit), e) if lit == e =>
        Some(obind(ob, e))

      case _ => None
    }

    matchesPattern(caze.pattern, scrut).flatMap { mapping =>
      caze.optGuard match {
        case Some(guard) =>
          if (e(guard)(rctx.withNewVars(mapping), gctx) == BooleanLiteral(true)) {
            Some(mapping)
          } else {
            None
          }
        case None =>
          Some(mapping)
      }
    }
  }
}

object RecursiveEvaluator {
  def apply(p: StainlessProgram, opts: inox.Options): RecursiveEvaluator { val program: p.type } = {
    new {
      val program: p.type = p
      val options = opts
    } with RecursiveEvaluator
      with inox.evaluators.HasDefaultGlobalContext
      with inox.evaluators.HasDefaultRecContext {

      val semantics = p.getSemantics
    }
  }

  def default(p: StainlessProgram) = apply(p, p.ctx.options)
}
