/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package verification

import purescala.Definitions.Program
import leon.evaluators.StringTracingEvaluator
import purescala.Expressions._
import purescala.Types.StringType
import leon.utils.DebugSectionSynthesis
import leon.utils.DebugSectionVerification
import leon.purescala.TypeOps

import leon.purescala.Quantification._
import purescala.Constructors._
import purescala.ExprOps._
import purescala.Expressions.Pattern
import purescala.Extractors._
import purescala.TypeOps._
import purescala.Types._
import purescala.Common._
import purescala.Expressions._
import purescala.Definitions._
import leon.solvers.{ HenkinModel, Model, SolverFactory }

object VerificationReport {
  /** If it can be computed, returns a user defined string for the given expression */
  def userDefinedString(v: Expr, orElse: =>String)(ctx: LeonContext, program: Program): String = {
    //println("Functions available:" + program.definedFunctions.map(fd => fd.id.name + "," + (fd.returnType == StringType) + ", " + (fd.params.length == 1) + "," + (fd.params.length == 1 && TypeOps.isSubtypeOf(v.getType, fd.params.head.getType)) + ", " + (if(fd.params.length == 1) fd.params.head.getType + " == " + v.getType else "")).mkString("\n"))
    (program.definedFunctions find {
      case fd => fd.returnType == StringType && fd.params.length == 1 && TypeOps.isSubtypeOf(v.getType, fd.params.head.getType) && fd.id.name.toLowerCase().endsWith("tostring")
    }) match {
      case Some(fd) =>
        //println("Found fd: " + fd.id.name)
        val ste = new StringTracingEvaluator(ctx, program)
        try {
        val result = ste.eval(FunctionInvocation(fd.typed, Seq(v)))
        
        result.result match {
          case Some((StringLiteral(res), _)) if res != "" =>
            res
          case _ =>
            orElse
        }
        } catch {
          case e: evaluators.ContextualEvaluator#EvalError =>
            orElse
        }
      case None =>
        //println("Function to render " + v + " not found")
        orElse
    }
  }
}

case class VerificationReport(program: Program, results: Map[VC, Option[VCResult]]) {

  val vrs: Seq[(VC, VCResult)] = results.toSeq.sortBy { case (vc, _) => (vc.fd.id.name, vc.kind.toString) }.map {
    case (vc, or) => (vc, or.getOrElse(VCResult.unknown))
  }

  lazy val totalConditions : Int = vrs.size

  lazy val totalTime: Long = vrs.map(_._2.timeMs.getOrElse(0l)).sum

  lazy val totalValid: Int   = vrs.count(_._2.isValid)
  lazy val totalInvalid: Int = vrs.count(_._2.isInvalid)
  lazy val totalUnknown: Int = vrs.count(_._2.isInconclusive)

  def summaryString : String = if(totalConditions >= 0) {
    import utils.ASCIIHelpers._

    var t = Table("Verification Summary")

    t ++= vrs.map { case (vc, vr) =>
      val timeStr = vr.timeMs.map(t => f"${t/1000d}%-3.3f").getOrElse("")
      Row(Seq(
        Cell(vc.fd.qualifiedName(program)),
        Cell(vc.kind.name),
        Cell(vc.getPos),
        Cell(vr.status),
        Cell(vr.solvedWith.map(_.name).getOrElse("")),
        Cell(timeStr, align = Right)
      ))
    }

    t += Separator

    t += Row(Seq(
      Cell(f"total: $totalConditions%-4d   valid: $totalValid%-4d   invalid: $totalInvalid%-4d   unknown $totalUnknown%-4d", 5),
      Cell(f"${totalTime/1000d}%7.3f", align = Right)
    ))

    t.render

  } else {
    "No verification conditions were analyzed."
  }
}
