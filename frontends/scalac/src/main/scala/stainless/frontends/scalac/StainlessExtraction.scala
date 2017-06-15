/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.scalac

import extraction.xlang.{trees => xt}
import MainHelpers.CompilerCallBack
import scala.tools.nsc._

/** Extract each compilation unit and forward them to the Compiler callback */
trait StainlessExtraction extends SubComponent with CodeExtraction {
  import global._

  val phaseName = "stainless"

  implicit val ctx: inox.Context
  protected val callback: CompilerCallBack

  def newPhase(prev: scala.tools.nsc.Phase): StdPhase = new Phase(prev)

  class Phase(prev: scala.tools.nsc.Phase) extends StdPhase(prev) {
    def apply(u: CompilationUnit): Unit = {
      val (unit, classes, functions) = extractUnit(u)
      callback(unit, classes, functions)
    }
  }
}
