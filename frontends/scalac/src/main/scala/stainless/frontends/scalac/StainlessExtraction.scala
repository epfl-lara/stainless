/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.scalac

import extraction.xlang.{trees => xt}
import frontend.MasterCallBack
import scala.tools.nsc._

import stainless.frontend.UnsupportedCodeException

/** Extract each compilation unit and forward them to the Compiler callback */
trait StainlessExtraction extends SubComponent with CodeExtraction with FragmentChecker {
  import global._

  val phaseName = "stainless"

  implicit val ctx: inox.Context
  protected val callback: MasterCallBack

  def newPhase(prev: scala.tools.nsc.Phase): StdPhase = new Phase(prev)

  class Phase(prev: scala.tools.nsc.Phase) extends StdPhase(prev) {
    def apply(u: CompilationUnit): Unit = {
      val file = u.source.file.absolute.path
      val checker = new Checker
      checker(u.body)
      if (!checker.hasErrors()) {
        val (unit, classes, functions) = extractUnit(u)
        callback(file, unit, classes, functions)
      }/* else
        // there seems to be some code that
        throw new UnsupportedCodeException(NoPosition, "Unsupported fragment detected")*/
    }
  }
}
