/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package termination

import purescala.Definitions._
import utils.ASCIIHelpers._

case class TerminationReport(ctx: LeonContext, results : Seq[(FunDef,TerminationGuarantee)], time : Double) {

  def summaryString : String = {
    var t = Table("Termination summary")

    for ((fd, g) <- results) t += Row(Seq(
      Cell(fd.id.asString(ctx)),
      Cell {
        val result = if (g.isGuaranteed) "\u2713" else "\u2717"
        val verdict = g match {
          case LoopsGivenInputs(reason, args) =>
            "Non-terminating for call: " + args.mkString(fd.id + "(", ",", ")")
          case CallsNonTerminating(funDefs) =>
            "Calls non-terminating functions " + funDefs.map(_.id).mkString(",")
          case Terminates(reason) =>
            "Terminates (" + reason + ")"
          case _ => g.toString
        }
        s"$result $verdict"
      }
    ))

    t += Separator

    t += Row(Seq(Cell(
      f"Analysis time: $time%7.3f",
      spanning = 2
    )))

    t.render
  }

  def evaluationString : String = {
    val sb = new StringBuilder
    for((fd,g) <- results) {
      val guar = g match {
        case NoGuarantee => "u"
        case t => if (t.isGuaranteed) "t" else "n"
      }
      sb.append(f"- ${fd.id.name}%-30s $guar\n")
    }
    sb.toString
  }
}
