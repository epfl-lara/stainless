/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import extraction.xlang.{ trees => xt }
import frontend.CallBackWithRegistry
import utils.CheckFilter

/** Callback for verification */
class VerificationCallBack(override val ctx: inox.Context) extends CallBackWithRegistry with CheckFilter {

  private implicit val debugSection = DebugSectionVerification

  override type Report = VerificationComponent.Report

  override def solve(program: Program { val trees: extraction.xlang.trees.type }): Report = {
    ctx.reporter.debug(
      s"Verifying the following program: " +
      "\n\tfunctions = [" + (program.symbols.functions.keySet mkString ", ") + "]" +
      "\n\tclasses   = [" + (program.symbols.classes.keySet mkString ", ") + "]"
    )

    VerificationComponent(program)
  }

}

