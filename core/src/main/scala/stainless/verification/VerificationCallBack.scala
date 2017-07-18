/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import extraction.xlang.{ trees => xt }

/** Callback for verification */
class VerificationCallBack(override val ctx: inox.Context) extends frontend.CallBackWithRegistry {

  override type Report = verification.VerificationComponent.Report

  override def solve(program: Program { val trees: extraction.xlang.trees.type }): Report = {
    verification.VerificationComponent(program)
  }

  /** Checks whether the given function/class should be verified at some point. */
  // TODO this check should be moved to a utility package and copy/past code removed from stainless.
  override def shouldBeChecked(fd: xt.FunDef): Boolean = {
    val isLibrary = fd.flags contains "library"
    val isUnchecked = fd.flags contains "unchecked"
    !(isLibrary || isUnchecked)
    // TODO check --functions=... options for proper filter
  }

  // Invariants are already extracted to functions, so no need to process the class unless it's a dependency.
  override def shouldBeChecked(cd: xt.ClassDef): Boolean = false

}

