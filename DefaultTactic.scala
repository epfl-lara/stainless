/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package verification

import purescala.Expressions._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Constructors._

class DefaultTactic(vctx: VerificationContext) extends Tactic(vctx) {
  val description = "Default verification condition generation approach"

  def generatePostconditions(fd: FunDef): Seq[VC] = {
    (fd.postcondition, fd.body) match {
      case (Some(post), Some(body)) =>
        val vc = implies(precOrTrue(fd), application(post, Seq(body)))
        Seq(VC(vc, fd, VCKinds.Postcondition).setPos(post))
      case _ =>
        Nil
    }
  }

  def generatePreconditions(fd: FunDef): Seq[VC] = {
    fd.body match {
      case Some(body) =>
        val calls = collectWithPC {
          case c @ FunctionInvocation(tfd, _) if tfd.hasPrecondition => (c, tfd.precondition.get)
        }(body)

        calls.map {
          case ((fi @ FunctionInvocation(tfd, args), pre), path) =>
            val pre2 = tfd.withParamSubst(args, pre)
            val vc = implies(and(precOrTrue(fd), path), pre2)
            val fiS = sizeLimit(fi.asString, 40)
            VC(vc, fd, VCKinds.Info(VCKinds.Precondition, s"call $fiS")).setPos(fi)
        }

      case None =>
        Nil
    }
  }

  def generateCorrectnessConditions(fd: FunDef): Seq[VC] = {

    def eToVCKind(e: Expr) = e match {
      case _ : MatchExpr =>
        VCKinds.ExhaustiveMatch

      case Assert(_, Some(err), _) =>
        if (err.startsWith("Map ")) {
          VCKinds.MapUsage
        } else if (err.startsWith("Array ")) {
          VCKinds.ArrayUsage
        } else if (err.startsWith("Division ")) {
          VCKinds.DivisionByZero
        } else if (err.startsWith("Modulo ")) {
          VCKinds.ModuloByZero
        } else if (err.startsWith("Remainder ")) {
          VCKinds.RemainderByZero
        } else if (err.startsWith("Cast ")) {
          VCKinds.CastError
        } else {
          VCKinds.Assert
        }

      case _ =>
        VCKinds.Assert
    }

    fd.body.toSeq.flatMap { body =>
      // We don't collect preconditions here, because these are handled by generatePreconditions
      val calls = collectCorrectnessConditions(body, collectFIs = false)

      calls.map {
        case (e, correctnessCond) =>
          val vc = implies(precOrTrue(fd), correctnessCond)

          VC(vc, fd, eToVCKind(e)).setPos(e)
      }
    }
  }

}
