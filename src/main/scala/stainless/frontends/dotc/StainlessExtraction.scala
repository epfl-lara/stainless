/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.dotc

import dotty.tools.dotc.ast.Trees._
import dotty.tools.dotc.core.Phases._
import dotty.tools.dotc.core.Contexts._

import scala.collection.mutable.ListBuffer

import extraction.xlang.{trees => xt}

class StainlessExtraction(inoxCtx: inox.Context) extends Phase {

  def phaseName: String = "stainless extraction"

  val symbols = new SymbolsContext

  private val units     = new ListBuffer[xt.UnitDef]
  private val classes   = new ListBuffer[xt.ClassDef]
  private val functions = new ListBuffer[xt.FunDef]

  def run(implicit ctx: Context): Unit = {
    val extraction = new CodeExtraction(inoxCtx, symbols)

    val unit = ctx.compilationUnit
    val tree = unit.tpdTree

    tree match {
      case pd @ PackageDef(_, _) =>
        val (unit, allClasses, allFunctions) = extraction.extractPackage(pd)
        units += unit
        classes ++= allClasses
        functions ++= allFunctions

      case _ =>
        println(tree)
    }
  }

  def getStructure: List[xt.UnitDef] = units.toList

  def getProgram: Program { val trees: xt.type } = new inox.Program {
    val ctx = inoxCtx
    val trees: xt.type = xt
    val symbols = xt.NoSymbols.withClasses(classes).withFunctions(functions)
  }
}
