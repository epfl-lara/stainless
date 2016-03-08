/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package verification

import purescala.Definitions.Program
import utils.Report

case class VerificationReport(program: Program, results: Map[VC, Option[VCResult]]) extends Report {
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
