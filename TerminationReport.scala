/* Copyright 2009-2013 EPFL, Lausanne */

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
      sb.append("- %-30s  %-30s\n".format(fd.id.name, g.toString))
    }
    sb.append("\n[Analysis time: %7.3f]\n".format(time))
    sb.toString
  }
}
