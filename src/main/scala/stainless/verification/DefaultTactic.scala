/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package verification

import purescala.Expressions._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Constructors._
import purescala.Extractors._
import leon.synthesis.ExamplesFinder

class DefaultTactic(vctx: VerificationContext) extends Tactic(vctx) {
  val description = "Default verification condition generation approach"

  def generatePostconditions(fd: FunDef): Seq[VC] = {
    (fd.postcondition, fd.body) match {
      case (Some(post), Some(body)) =>
        val newpost = if(post match { case Lambda(vd, tla@TopLevelAnds(conjuncts)) => conjuncts.exists(_.isInstanceOf[Passes]) case _ => false}) {
          val ef = new ExamplesFinder(vctx, vctx.program)
          val examples = ef.extractFromFunDef(fd, true)
          val examplesConditions = examples.invalids.collect{
             case synthesis.InOutExample(in, out) =>
               not(and(fd.paramIds.zip(in).map{ idVal => Equals(Variable(idVal._1), idVal._2)}: _*))
          }

          post match {
            case Lambda(vd, tla@TopLevelAnds(conjuncts)) =>
              Lambda(vd, and(examplesConditions ++ conjuncts.filterNot(ExamplesFinder.isConcretelyTestablePasses) :_*).copiedFrom(tla)
              ).copiedFrom(post)
          }}
          else post
        
        val vc = implies(fd.precOrTrue, application(newpost, Seq(body)))
        Seq(VC(vc, fd, VCKinds.Postcondition).setPos(post))
      case _ =>
        Nil
    }
  }

  def generatePreconditions(fd: FunDef): Seq[VC] = {

    val calls = collectWithPC {
      case c @ FunctionInvocation(tfd, _) if tfd.hasPrecondition =>
        c
    }(fd.fullBody)

    calls.map {
      case (fi @ FunctionInvocation(tfd, args), path) =>
        val pre = tfd.withParamSubst(args, tfd.precondition.get)
        val vc = path implies pre
        val fiS = sizeLimit(fi.asString, 40)
        VC(vc, fd, VCKinds.Info(VCKinds.Precondition, s"call $fiS")).setPos(fi)
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

    // We don't collect preconditions here, because these are handled by generatePreconditions
    val calls = collectCorrectnessConditions(fd.fullBody)

    calls.map {
      case (e, correctnessCond) =>
        VC(correctnessCond, fd, eToVCKind(e)).setPos(e)
    }
  }


}
