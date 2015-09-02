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
      fd.body match {
        case Some(body) =>
          val calls = collectWithPC {

            case m @ MatchExpr(scrut, cases) =>
              (m, VCKinds.ExhaustiveMatch, orJoin(cases map (matchCaseCondition(scrut, _))))

            case e @ Error(_, _) =>
              (e, VCKinds.Assert, BooleanLiteral(false))

            case a @ Assert(cond, Some(err), _) => 
              val kind = if (err.startsWith("Map ")) {
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

              (a, kind, cond)
            case a @ Assert(cond, None, _) => (a, VCKinds.Assert, cond)
            // Only triggered for inner ensurings, general postconditions are handled by generatePostconditions
            case a @ Ensuring(body, post) => (a, VCKinds.Assert, application(post, Seq(body)))
          }(body)

          calls.map {
            case ((e, kind, correctnessCond), path) =>
              val vc = implies(and(precOrTrue(fd), path), correctnessCond)

              VC(vc, fd, kind).setPos(e)
          }

        case None =>
          Nil
      }
    }
}
