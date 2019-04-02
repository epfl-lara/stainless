/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package frontends.scalac

import extraction.xlang.{trees => xt}
import scala.tools.nsc._

import stainless.frontend.{ UnsupportedCodeException, CallBack }

/** Extract each compilation unit and forward them to the Compiler callback */
trait StainlessExtraction extends SubComponent with CodeExtraction with FragmentChecker {
  import global._

  val phaseName = "stainless"

  implicit val ctx: inox.Context
  protected val callback: CallBack

  def newPhase(prev: scala.tools.nsc.Phase): StdPhase = new Phase(prev)

  class Phase(prev: scala.tools.nsc.Phase) extends StdPhase(prev) {
    def apply(u: CompilationUnit): Unit = {
      val file = u.source.file.absolute.path
      val checker = new Checker
      checker(u.body)

      // then check ghost accesses
      val ghostChecker = new GhostAnnotationChecker
      ghostChecker(u.body)

      if (!hasErrors()) {
        val (unit, classes, functions, typeDefs) = extractUnit(u)
        callback(file, unit, classes, functions, typeDefs)
      }
    }
  }
}
