/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package verification

import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Definitions._

import scala.collection.mutable.{Map => MutableMap}

class DefaultTactic(vctx: VerificationContext) extends Tactic(vctx) {
    val description = "Default verification condition generation approach"
    override val shortDescription = "default"

    def generatePostconditions(fd: FunDef): Seq[VerificationCondition] = {
      (fd.postcondition, fd.body) match {
        case (Some((id, post)), Some(body)) =>
          val res = id.freshen
          val vc = Implies(precOrTrue(fd), Let(res, safe(body), replace(Map(id.toVariable -> res.toVariable), safe(post))))

          Seq(new VerificationCondition(vc, fd, VCKind.Postcondition, this).setPos(post))
        case _ =>
          Nil
      }
    }
  
    def generatePreconditions(fd: FunDef): Seq[VerificationCondition] = {
      fd.body match {
        case Some(body) =>
          val calls = collectWithPC {
            case c @ FunctionInvocation(tfd, _) if tfd.hasPrecondition => (c, tfd.precondition.get)
          }(safe(body))

          calls.map {
            case ((fi @ FunctionInvocation(tfd, args), pre), path) =>
              val pre2 = replaceFromIDs((tfd.params.map(_.id) zip args).toMap, safe(pre))
              val vc = Implies(And(precOrTrue(fd), path), pre2)

              new VerificationCondition(vc, fd, VCKind.Precondition, this).setPos(fi)
          }

        case None =>
          Nil
      }
    }

    def generateCorrectnessConditions(fd: FunDef): Seq[VerificationCondition] = {
      fd.body match {
        case Some(body) =>
          val calls = collectWithPC {
            case e @ Error(_) => (e, BooleanLiteral(false))
            case a @ Assert(cond, _, _) => (a, cond)
            // Only triggered for inner ensurings, general postconditions are handled by generatePostconditions
            case a @ Ensuring(body, id, post) => (a, Let(id, body, post))
          }(safe(body))

          calls.map {
            case ((e, errorCond), path) =>
              val vc = Implies(And(precOrTrue(fd), path), errorCond)

              new VerificationCondition(vc, fd, VCKind.Correctness, this).setPos(e)
          }

        case None =>
          Nil
      }
    }
}
