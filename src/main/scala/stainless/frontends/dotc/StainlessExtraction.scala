/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.dotc

import dotty.tools.dotc.ast.Trees._
import dotty.tools.dotc.core.Phases._
import dotty.tools.dotc.core.Contexts._

import scala.collection.mutable.ListBuffer

class StainlessExtraction(inoxCtx: inox.Context) extends Phase {

  def phaseName: String = "stainless extraction"

  val symbols = new SymbolsContext

  private val packages  = new ListBuffer[xlang.trees.PackageDef]
  private val classes   = new ListBuffer[xlang.trees.ClassDef]
  private val functions = new ListBuffer[xlang.trees.FunDef]

  def run(implicit ctx: Context): Unit = {
    val extraction = new CodeExtraction(inoxCtx, symbols)

    val unit = ctx.compilationUnit
    val tree = unit.tpdTree

    tree match {
      case pd @ PackageDef(_, _) =>
        val (pkg, allClasses, allFunctions) = extraction.extractPackage(pd)
        packages += pkg
        classes ++= allClasses
        functions ++= allFunctions

      case _ =>
        println(tree)
    }
  }

  def getStructure: List[xlang.trees.PackageDef] = packages.toList

  def getProgram: Program { val trees: xlang.trees.type } = new inox.Program {
    val ctx = inoxCtx
    val trees: xlang.trees.type = xlang.trees
    val symbols = xlang.trees.NoSymbols.withClasses(classes).withFunctions(functions)
  }
}
