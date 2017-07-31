/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package utils

import extraction.xlang.{ trees => xt }

/** Filter functions / classes for verification purposes */
trait CheckFilter {

  val ctx: inox.Context

  /** Checks whether the given function/class should be verified at some point. */
  def shouldBeChecked(fd: xt.FunDef): Boolean = {
    val isLibrary = fd.flags contains "library"
    val isUnchecked = fd.flags contains "unchecked"
    !(isLibrary || isUnchecked)
    // TODO check --functions=... options for proper filter
  }

  // Invariants are already extracted to functions, so no need to process the class unless it's a dependency.
  def shouldBeChecked(cd: xt.ClassDef): Boolean = false

}

