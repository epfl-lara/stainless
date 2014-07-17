/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package verification

import purescala.Definitions.FunDef

class VerificationReport(val fvcs: Map[FunDef, List[VerificationCondition]]) {
  import scala.math.Ordering.Implicits._
  val conditions : Seq[VerificationCondition] = fvcs.flatMap(_._2).toSeq.sortBy(vc => (vc.funDef.id.name, vc.kind.toString))

  lazy val totalConditions : Int = conditions.size

  lazy val totalTime : Double = conditions.foldLeft(0.0d)((t,c) => t + c.time.getOrElse(0.0d))

  lazy val totalValid : Int = conditions.count(_.value == Some(true))

  lazy val totalInvalid : Int = conditions.count(_.value == Some(false))

  lazy val totalUnknown : Int = conditions.count(_.value == None)

  def summaryString : String = if(totalConditions >= 0) {
    import utils.ASCIITables._

    var t = Table("Verification Summary")

    t ++= conditions.map { vc =>
      val timeStr = vc.time.map(t => "%-3.3f".format(t)).getOrElse("")
      Row(Seq(
        Cell(vc.funDef.id.toString),
        Cell(vc.kind),
        Cell(vc.status),
        Cell(vc.tacticStr),
        Cell(vc.solverStr),
        Cell(timeStr, align = Right)
      ))
    }

    t += Separator

    t += Row(Seq(
      Cell(f"total: $totalConditions%-4d   valid: $totalValid%-4d   invalid: $totalInvalid%-4d   unknown $totalUnknown%-4d", 5),
      Cell(f"$totalTime%7.3f", align = Right)
    ))

    t.render

  } else {
    "No verification conditions were analyzed."
  }
}
