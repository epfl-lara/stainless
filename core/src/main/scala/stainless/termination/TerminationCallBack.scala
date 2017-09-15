/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import frontend.CallBackWithRegistry
import utils.CheckFilter

import io.circe.Json

/** Callback for termination */
final class TerminationCallBack(override val context: inox.Context) extends CallBackWithRegistry with CheckFilter {
  private implicit val debugSection = DebugSectionTermination

  override type Report = TerminationReport
  override val cacheSubDirectory = TerminationComponent.name
  override def parseReportCache(json: Json): Report = TerminationReport.parse(json)

  override def onCycleBegin(): Unit = TerminationComponent.onCycleBegin()

  override def solve(program: Program { val trees: extraction.xlang.trees.type }): Report = {
    context.reporter.debug(
      s"Checking termination fo the following program: " +
      "\n\tfunctions = [" + (program.symbols.functions.keySet mkString ", ") + "]" +
      "\n\tclasses   = [" + (program.symbols.classes.keySet mkString ", ") + "]"
    )

    TerminationComponent(program, context).toReport
  }

}

