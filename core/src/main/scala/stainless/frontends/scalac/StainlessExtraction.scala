/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.scalac

import scala.tools.nsc._

trait StainlessExtraction extends SubComponent with CodeExtraction {
  import global._

  val phaseName = "stainless"

  var units: List[CompilationUnit] = Nil
  
  implicit val ctx: inox.Context

  var imports : Map[RefTree,List[Import]] = Map()
  
  def setImports(imports : Map[RefTree, List[Import]]) {
    this.imports = imports
  }

  def extractProgram = {
    new Extraction(units).extractProgram
  }

  def newPhase(prev: scala.tools.nsc.Phase): StdPhase = new Phase(prev)

  class Phase(prev: scala.tools.nsc.Phase) extends StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      units ::= unit
    }
  }
}
