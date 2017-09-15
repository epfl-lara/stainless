/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import extraction.xlang.{ trees => xt }
import frontend.CallBackWithRegistry
import utils.CheckFilter

/** Callback for verification */
final class VerificationCallBack(override val context: inox.Context) extends CallBackWithRegistry with CheckFilter {

  private implicit val debugSection = DebugSectionVerification

  override type Report = VerificationReport
  override val cacheSubDirectory = VerificationComponent.name
  override def parseReportCache(json: org.json4s.JValue): Report = VerificationReport.parse(json)

  override def onCycleBegin(): Unit = VerificationComponent.onCycleBegin()

  override def solve(program: Program { val trees: extraction.xlang.trees.type }): Report = {
    context.reporter.debug(
      s"Verifying the following program: " +
      "\n\tfunctions = [" + (program.symbols.functions.keySet mkString ", ") + "]" +
      "\n\tclasses   = [" + (program.symbols.classes.keySet mkString ", ") + "]"
    )

    VerificationComponent(program, context).toReport
  }

}

