/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package termination

import frontend.CallBackWithRegistry
import utils.CheckFilter

import scala.concurrent.Future

import io.circe.Json

/** Callback for termination */
final class TerminationCallBack(override implicit val context: inox.Context)
  extends CallBackWithRegistry with CheckFilter {

  private implicit val debugSection = DebugSectionTermination

  override type Report = TerminationReport
  override val cacheSubDirectory = TerminationComponent.name
  override def parseReportCache(json: Json): Report = TerminationReport.parse(json)

  override def onCycleBegin(): Unit = TerminationComponent.onCycleBegin()

  override def solve(program: Program { val trees: extraction.xlang.trees.type }): Future[Report] = {
    context.reporter.debug(
      s"Checking termination fo the following program: " +
      "\n\tfunctions = [" + (program.symbols.functions.keySet mkString ", ") + "]" +
      "\n\tclasses   = [" + (program.symbols.classes.keySet mkString ", ") + "]"
    )

    TerminationComponent(program, context).map(_.toReport)
  }

}

