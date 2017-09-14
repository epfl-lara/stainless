/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package termination

import extraction.xlang.{ trees => xt }
import frontend.CallBackWithRegistry
import utils.CheckFilter

/** Callback for termination */
class TerminationCallBack(override val context: inox.Context) extends CallBackWithRegistry with CheckFilter {
  private implicit val debugSection = DebugSectionTermination

  override type Report = TerminationComponent.Report

  final override def beginExtractions(): Unit = TerminationComponent.onCycleBegin()

  override def solve(program: Program { val trees: extraction.xlang.trees.type }): Report = {
    context.reporter.debug(
      s"Checking termination fo the following program: " +
      "\n\tfunctions = [" + (program.symbols.functions.keySet mkString ", ") + "]" +
      "\n\tclasses   = [" + (program.symbols.classes.keySet mkString ", ") + "]"
    )

    TerminationComponent(program, context)
  }
}

