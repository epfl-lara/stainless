/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package termination

import purescala.Definitions._

object TerminationPhase extends LeonPhase[Program,TerminationReport] {
  val name = "Termination"
  val description = "Check termination of PureScala functions"

  def run(ctx : LeonContext)(program : Program) : TerminationReport = {
    val tc = new SimpleTerminationChecker(ctx, program)

    val startTime = System.currentTimeMillis
    val results = program.definedFunctions.toList.sortWith(_ < _).map { funDef =>
      (funDef -> tc.terminates(funDef))
    }
    val endTime = System.currentTimeMillis
    new TerminationReport(results, (endTime - startTime).toDouble / 1000.0d)
  } 
}
