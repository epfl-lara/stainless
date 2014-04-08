/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package verification

import purescala.Definitions.FunDef

class VerificationReport(val fvcs: Map[FunDef, List[VerificationCondition]]) {
  import scala.math.Ordering.Implicits._
  val conditions : Seq[VerificationCondition] = fvcs.flatMap(_._2).toSeq.sortBy(vc => (vc.funDef.id.name, vc.kind))

  lazy val totalConditions : Int = conditions.size

  lazy val totalTime : Double = conditions.foldLeft(0.0d)((t,c) => t + c.time.getOrElse(0.0d))

  lazy val totalValid : Int = conditions.count(_.value == Some(true))

  lazy val totalInvalid : Int = conditions.count(_.value == Some(false))

  lazy val totalUnknown : Int = conditions.count(_.value == None)

  def summaryString : String = if(totalConditions >= 0) {
    VerificationReport.infoHeader +
    conditions.map(VerificationReport.infoLine).mkString("\n", "\n", "\n") +
    VerificationReport.infoSep +
    ("║ total: %-4d   valid: %-4d   invalid: %-4d   unknown %-4d " +
      (" " * 16) +
      " %7.3f ║\n").format(totalConditions, totalValid, totalInvalid, totalUnknown, totalTime) +
    VerificationReport.infoFooter
  } else {
    "No verification conditions were analyzed."
  }
}

object VerificationReport {
  def emptyReport : VerificationReport = new VerificationReport(Map())

  private def fit(str : String, maxLength : Int) : String = {
    if(str.length <= maxLength) {
      str
    } else {
      str.substring(0, maxLength - 1) + "…"
    }
  }

  private val infoSep    : String = "╟" + ("┄" * 83) + "╢\n"
  private val infoFooter : String = "╚" + ("═" * 83) + "╝"
  private val infoHeader : String = ". ┌─────────┐\n" +
                                    "╔═╡ Summary ╞" + ("═" * 71) + "╗\n" +
                                    "║ └─────────┘" + (" " * 71) + "║"

  private def infoLine(vc : VerificationCondition) : String = {
    val timeStr = vc.time.map(t => "%-3.3f".format(t)).getOrElse("")

    "║ %-25s %-9s %9s %-8s %-10s %-7s %7s ║".format(
      fit(vc.funDef.id.toString, 25),
      vc.kind,
      vc.getPos,
      vc.status,
      vc.tacticStr,
      vc.solverStr,
      timeStr)
  }
}
