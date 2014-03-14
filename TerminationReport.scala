/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package termination

import purescala.Definitions._

case class TerminationReport(val results : Seq[(FunDef,TerminationGuarantee)], val time : Double) {
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
      sb.append("- %-30s %s %-30s\n".format(fd.id.name, result, toPrint))
    }
    sb.append("\n[Analysis time: %7.3f]\n".format(time))
    sb.toString
  }

  def evaluationString : String = {
    val sb = new StringBuilder
    for((fd,g) <- results) {
      sb.append("- %-30s %s\n".format(fd.id.name, g match {
        case NoGuarantee => "u"
        case t => if (t.isGuaranteed) "t" else "n"
      }))
    }
    sb.toString
  }
}
