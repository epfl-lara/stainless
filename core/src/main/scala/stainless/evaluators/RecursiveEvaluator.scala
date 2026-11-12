/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package evaluators

abstract class RecursiveEvaluator(override val program: Program,
                                  override val context: inox.Context)
                                 (using override protected val semantics: program.Semantics)
  extends inox.evaluators.RecursiveEvaluator(program, context) with ChooseSolving {
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  /** The choose that is the body of the function `id`, which the model gives as an uninterpreted
    * function of the function's parameters (see [[solvers.InoxEncoder]]). */
  private def liftedChoose(id: Identifier): Option[Choose] = getFunction(id).fullBody match {
    case c: Choose => Some(c)
    case _ => None
  }

  override def e(expr: Expr)(using rctx: RC, gctx: GC): Expr = expr match {
    case FunctionInvocation(id, tps, args) if liftedChoose(id).isDefined =>
      val Choose(res, _) = liftedChoose(id).get: @unchecked
      rctx.interpretations.get(res.id -> tps) match {
        case Some(l: Lambda) if l.params.size == args.size =>
          e(l.body)(using rctx.withNewVars(l.paramSubst(args.map(e))), gctx)
        case _ => super.e(expr)
      }

    // The model gives a choose as the uninterpreted function of its free variables that encodes it
    // (see [[solvers.InoxEncoder]]), and the chooses it doesn't give are solved for
    case c: Choose =>
      val call = exprOps.chooseCall(c)
      rctx.interpretations.get(call.id -> call.tps) match {
        case Some(l: Lambda) if l.params.size == call.args.size =>
          e(l.body)(using rctx.withNewVars(l.paramSubst(call.args.map(e))), gctx)
        case _ =>
          onChooseInvocation(exprOps.replaceFromSymbols(exprOps.variablesOf(c).map(v => v -> e(v)).toMap, c).asInstanceOf[Choose], rctx.interpretations)
      }

    case Require(pred, body) =>
      if (!ignoreContractsOn(expr) && e(pred) != BooleanLiteral(true))
        throw RuntimeError("Requirement did not hold @" + expr.getPos)
      e(body)

    case en @ Ensuring(body, pred) =>
      e(en.toAssert)

    case Decreases(measure, body) =>
      e(body)

    case Assert(pred, err, body) =>
      if (!ignoreContractsOn(expr) && e(pred) != BooleanLiteral(true))
        throw RuntimeError(err.getOrElse("Assertion failed @" + expr.getPos))
      e(body)

    case MatchExpr(scrut, cases) =>
      val rscrut = e(scrut)
      cases.to(LazyList).map(c => matchesCase(rscrut, c).map(c -> _)).find(_.nonEmpty) match {
        case Some(Some((c, mapping))) => e(c.rhs)(using rctx.withNewVars(mapping), gctx)
        case _ => throw RuntimeError("MatchError: " + rscrut + " did not match any of the cases:\n" + cases)
      }

    case p: Passes =>
      e(p.asConstraint)

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
        elems.getOrElse(i, default)
      case (_, _) => throw RuntimeError("ArraySelect on non-array or non-integer index @" + expr.getPos)
    }

    case ArrayUpdated(array, index, value) => (e(array), e(index)) match {
      case (FiniteArray(elems, base), Int32Literal(i)) =>
        if (i < 0 || i >= elems.size) throw RuntimeError("Index out of bounds @" + expr.getPos)
        FiniteArray(elems.updated(i, e(value)), base)
      case (LargeArray(elems, default, s @ Int32Literal(size), base), Int32Literal(i)) =>
        if (i < 0 || i >= size) throw RuntimeError("Index out of bounds @" + expr.getPos)
        LargeArray(elems + (i -> e(value)), default, s, base)
      case (_, _) => throw RuntimeError("ArrayUpdated on non-array or non-integer index @" + expr.getPos)
    }

    case ArrayLength(array) => e(array) match {
      case FiniteArray(elems, _) => Int32Literal(elems.size)
      case LargeArray(_, _, s, _) => s
    }

    case m: Max =>
      e(maxToIfThenElse(m))

    // In Stainless, `Division` and `Remainder` on integers are the JVM's `BigInt./` and `BigInt.%`, which
    // round toward zero (Inox's are SMT-LIB's euclidean `div` and `mod`, see InoxEncoder)
    case Division(l, r) if expr.getType == IntegerType() => (e(l), e(r)) match {
      case (IntegerLiteral(i1), IntegerLiteral(i2)) =>
        if (i2 != 0) IntegerLiteral(i1 / i2) else throw RuntimeError("Division by 0.")
      case (le, re) => throw EvalError("Unexpected operation: (" + le.asString + ") / (" + re.asString + ")")
    }

    case Remainder(l, r) if expr.getType == IntegerType() => (e(l), e(r)) match {
      case (IntegerLiteral(i1), IntegerLiteral(i2)) =>
        if (i2 != 0) IntegerLiteral(i1 % i2) else throw RuntimeError("Remainder of division by 0.")
      case (le, re) => throw EvalError("Unexpected operation: (" + le.asString + ") % (" + re.asString + ")")
    }

    // the bit-vector shifts of inox follow SMT-LIB: the amount has to be taken modulo the width first
    case shift: JVMShift =>
      e(shift.masked)

    case Error(tpe, msg) =>
      throw RuntimeError("Error reached in evaluation: " + msg)

    case NoTree(tpe) =>
      throw RuntimeError("Reached empty tree in evaluation @" + expr.getPos)

    case Annotated(body, flags) =>
      val nrctx = {
        if (flags.contains(DropVCs) || flags.contains(DropConjunct)) rctx.withLocallyIgnoredContracts
        else rctx
      }
      e(body)(using nrctx)

    case _ => super.e(expr)
  }

  override def ignoreContractsOn(expr: Expr)(using rctx: RC, gctx: GC): Boolean = {
    def isAnnotatedDrop(e: Expr) = e match {
      case Annotated(_, flags) => flags.contains(DropVCs) || flags.contains(DropConjunct)
      case _ => false
    }

    super.ignoreContractsOn(expr) || (expr match {
      case Assume(pred, _) => isAnnotatedDrop(pred)
      case Assert(pred, _, _) => isAnnotatedDrop(pred)
      case Require(pred, _) => isAnnotatedDrop(pred)
      case Ensuring(_, pred) => isAnnotatedDrop(pred) || isAnnotatedDrop(pred.body)
      case _ => isAnnotatedDrop(expr)
    })
  }

  protected def matchesCase(scrut: Expr, caze: MatchCase)
                           (using rctx: RC, gctx: GC): Option[Map[ValDef, Expr]] = {

    def obind(ob: Option[ValDef], e: Expr): Map[ValDef, Expr] = {
      Map.empty[ValDef, Expr] ++ ob.map(_ -> e)
    }

    def matchesPattern(pat: Pattern, expr: Expr): Option[Map[ValDef, Expr]] = (pat, expr) match {
      case (WildcardPattern(ob), e) =>
        Some(obind(ob, e))

      case (ADTPattern(ob, id, tps, subs), ADT(id2, tps2, args)) =>
        if (id == id2 && tps == tps2) {
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

      case (AlternativePattern(ob, subs), scrut) =>
        subs.map(matchesPattern(_, scrut)).find(_.isDefined) match {
          case Some(_) => Some(obind(ob, expr)) // There should be no mapping nested in the alternative
          case _ => None
        }

      case (RefinementPattern(underlying, Lambda(vds, pred)), scrut) =>
        val Seq(vd) = vds: @unchecked
        matchesPattern(underlying, scrut).flatMap { mapping =>
          if (e(pred)(using rctx.withNewVar(vd, scrut), gctx) == BooleanLiteral(true)) {
            Some(mapping + (vd -> scrut))
          } else {
            None
          }
        }

      case (up @ UnapplyPattern(ob, rec, id, tps, subs), scrut) =>
        val eRec = rec map e
        val unapp = e(FunctionInvocation(id, tps, eRec :+ scrut))
        e(up.isEmptyUnapplied(unapp)) match {
          case BooleanLiteral(false) =>
            val extracted = e(up.getUnapplied(unapp))
            val res = (subs zip unwrapTuple(extracted, subs.size)) map (p => matchesPattern(p._1, p._2))
            if (res.forall(_.isDefined)) {
              Some(obind(ob, expr) ++ res.flatten.flatten)
            } else {
              None
            }
          case BooleanLiteral(true) => None
          case other => throw EvalError(typeErrorMsg(other, BooleanType()))
        }

      case (LiteralPattern(ob, lit), e) if lit == e =>
        Some(obind(ob, e))

      case _ => None
    }

    matchesPattern(caze.pattern, scrut).flatMap { mapping =>
      caze.optGuard match {
        case Some(guard) =>
          if (e(guard)(using rctx.withNewVars(mapping), gctx) == BooleanLiteral(true)) {
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
  def apply(p: StainlessProgram, ctx: inox.Context): RecursiveEvaluator { val program: p.type } = {
    class Impl(override val program: p.type) extends RecursiveEvaluator(program, ctx)(using p.getSemantics)
      with inox.evaluators.HasDefaultGlobalContext
      with inox.evaluators.HasDefaultRecContext
    new Impl(p)
  }
}
