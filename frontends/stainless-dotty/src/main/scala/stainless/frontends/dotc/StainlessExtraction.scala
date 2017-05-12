/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.dotc

import dotty.tools.dotc.ast.tpd
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
    import extraction.{ctx => _, _}
    import AuxiliaryExtractors._

    val unit = ctx.compilationUnit
    val tree = unit.tpdTree
    val (id, stats) = tree match {
      case pd @ PackageDef(refTree, lst) =>
        val id = lst.collectFirst { case PackageDef(ref, stats) => ref } match {
          case Some(ref) => extractRef(ref)
          case None => FreshIdentifier(unit.source.file.name.replaceFirst("[.][^.]+$", ""))
        }
        (id, pd.stats)
      case _ => outOfSubsetError(tree, "Unexpected unit body")
    }

    val (imports, unitClasses, unitFunctions, subs, allClasses, allFunctions) = extraction.extractStatic(stats)
    assert(unitFunctions.isEmpty, "Packages shouldn't contain functions")

    val isLibrary = Main.libraryFiles contains unit.source.file.absolute.path
    units += xt.UnitDef(id, imports, unitClasses, subs, !isLibrary)
    classes ++= allClasses
    functions ++= allFunctions
  }

  def getStructure: List[xt.UnitDef] = units.toList

  def getProgram: Program { val trees: xt.type } = new inox.Program {
    val ctx = inoxCtx
    val trees: xt.type = xt
    val symbols = xt.NoSymbols.withClasses(classes).withFunctions(functions)
  }
}
