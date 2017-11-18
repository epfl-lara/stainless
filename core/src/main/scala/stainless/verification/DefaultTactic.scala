/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

trait DefaultTactic extends Tactic {
  val description = "Default verification condition generation approach"

  import context._
  import program._
  import program.trees._
  import program.symbols._

  def generatePostconditions(id: Identifier): Seq[VC] = {
    val fd = getFunction(id)
    (fd.postcondition, fd.body) match {
      case (Some(post), Some(body)) =>
        val vc = exprOps.freshenLocals(implies(fd.precOrTrue, application(post, Seq(body))))
        Seq(VC(vc, id, VCKind.Postcondition).setPos(post))
      case _ =>
        Nil
    }
  }

  def generatePreconditions(id: Identifier): Seq[VC] = {
    val fd = getFunction(id)

    val calls = collectForConditions {
      case (fi: FunctionInvocation, path) if fi.tfd.precondition.isDefined => (fi, path)
    }(fd.fullBody)

    calls.map { case (fi @ FunctionInvocation(_, _, args), path) =>
      val pre = fi.tfd.withParamSubst(args, fi.tfd.precondition.get)
      val vc = path implies exprOps.freshenLocals(pre)
      val fiS = sizeLimit(fi.asString, 40)
      VC(vc, id, VCKind.Info(VCKind.Precondition, s"call $fiS")).setPos(fi)
    }
  }

  def generateCorrectnessConditions(id: Identifier): Seq[VC] = {

    def eToVCKind(e: Expr) = e match {
      case _ : MatchExpr =>
        VCKind.ExhaustiveMatch

      case Assert(_, Some(err), _) =>
        if (err.startsWith("Array ")) {
          VCKind.ArrayUsage
        } else if (err.startsWith("Map ")) {
          VCKind.MapUsage
        } else if (err.endsWith("Overflow")) {
          VCKind.Overflow
        } else if (err.startsWith("Shift")) {
          VCKind.Shift
        } else if (err.startsWith("Division ")) {
          VCKind.DivisionByZero
        } else if (err.startsWith("Modulo ")) {
          VCKind.ModuloByZero
        } else if (err.startsWith("Remainder ")) {
          VCKind.RemainderByZero
        } else if (err.startsWith("Cast ")) {
          VCKind.CastError
        } else {
          VCKind.AssertErr(err)
        }

      case _: Choose =>
        VCKind.Choose

      case _: ADT =>
        VCKind.AdtInvariant

      case _ =>
        VCKind.Assert
    }

    // We don't collect preconditions here, because these are handled by generatePreconditions
    val calls = collectForConditions {
      case (m @ MatchExpr(scrut, cases), path) =>
        (m, path implies orJoin(cases map (matchCaseCondition[Path](scrut, _).toClause)))

      case (e @ Error(_, _), path) =>
        (e, Not(path.toClause))

      case (a @ Assert(cond, _, _), path) =>
        (a, path implies cond)

      case (c @ Choose(res, pred), path) if !(res.flags contains Unchecked) =>
        (c, path implies Not(Forall(Seq(res), Not(pred))))

      case (a @ ADT(tpe, args), path) if tpe.getADT.hasInvariant =>
        (a, path implies FunctionInvocation(tpe.getADT.invariant.get.id, tpe.tps, Seq(a)))
    }(getFunction(id).fullBody)

    calls.map { case (e, correctnessCond) =>
      VC(correctnessCond, id, eToVCKind(e)).setPos(e)
    }
  }
}

object DefaultTactic {
  def apply(p: StainlessProgram, ctx: inox.Context): DefaultTactic { val program: p.type } = new DefaultTactic {
    val program: p.type = p
    val context = ctx
  }
}
