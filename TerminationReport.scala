/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package termination

import purescala.Definitions._

case class TerminationReport(results : Seq[(FunDef,TerminationGuarantee)], time : Double) {
  def summaryString : String = {
    val sb = new StringBuilder
    sb.append("─────────────────────\n")
    sb.append(" Termination summary \n")
    sb.append("─────────────────────\n\n")
    for((fd,g) <- results) {
      val result = if (g.isGuaranteed) "\u2713" else "\u2717"
      val toPrint = g match {
        case LoopsGivenInputs(reason, args) =>
          "Non-terminating for call: " + args.mkString(fd.id+"(", ",", ")")
        case CallsNonTerminating(funDefs) =>
          "Calls non-terminating functions " + funDefs.map(_.id).mkString(",")
        case Terminates(reason) =>
          "Terminates (" + reason + ")"
        case _ => g.toString
      }
      sb.append(f"- ${fd.id.name}%-30s $result $toPrint%-30s\n")
    }
    sb.append(f"\n[Analysis time: $time%7.3f]\n")
    sb.toString
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
