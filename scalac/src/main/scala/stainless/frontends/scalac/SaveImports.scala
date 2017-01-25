/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.scalac

import scala.tools.nsc._

trait SaveImports extends SubComponent {
  import global._

  val phaseName = "imports"

  val ctx: inox.Context

  var imports : Map[RefTree,List[Import]] = Map()

  implicit val debugSection = inox.ast.DebugSectionTrees
  
  // FIXME : Copy pasting code is bad.
  def scalaPosToStainlessPos(p: global.Position): inox.utils.Position = {
    if (p == NoPosition) {
      inox.utils.NoPosition
    } else if (p.isRange) {
      val start = p.focusStart
      val end   = p.focusEnd
      inox.utils.RangePosition(start.line, start.column, start.point,
                               end.line, end.column, end.point,
                               p.source.file.file)
    } else {
      inox.utils.OffsetPosition(p.line, p.column, p.point,
                                p.source.file.file)
    }
  }

  def newPhase(prev: scala.tools.nsc.Phase): StdPhase = new Phase(prev)

  class Phase(prev: scala.tools.nsc.Phase) extends StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      unit.body match {
        case pkg @ PackageDef(pid,lst) =>
          
          imports += pid -> (lst collect { 
            case i: Import => i
          })
          
          for (tree <- lst if !tree.isInstanceOf[Import] ) {
            tree.foreach {
              case imp: Import =>
                ctx.reporter.debug(
                  scalaPosToStainlessPos(imp.pos),
                  "Note: Imports will not be preserved in the AST unless they are at top-level"
                )
              case _ => 
            }
          }
          
      }
    }
  }
}
