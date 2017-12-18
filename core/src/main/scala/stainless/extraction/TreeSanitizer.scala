/* Copyright 2009-2017 EPFL, Lausanne */

package stainless
package extraction

import xlang.{ trees => xt }

/** Inspect trees, detecting illegal structures. */
object TreeSanitizer {

  import xt.exprOps

  /** Throw a [[MissformedStainlessCode]] exception when detecting an illegal pattern. */
  def check(program: Program { val trees: xt.type }): Unit = {
    val funs = program.symbols.functions.values
    funs foreach checkPrecondition
  }

  // This detects both multiple `require` and `require` after `decreases`.
  private def checkPrecondition(fd: xt.FunDef): Unit = {
    exprOps withoutSpecs fd.fullBody foreach { bareBody =>
      exprOps.exists {
        case e: xt.Require =>
          throw MissformedStainlessCode(e, s"${fd.id} contains an unexpected `require`.")

        case e: xt.Decreases =>
          throw MissformedStainlessCode(e, s"${fd.id} contains an unexpected `decreases`.")

        case _ => false
      }(bareBody)
    }
  }

}

