/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.dotty

import dotty.tools.dotc.ast.Trees._
import dotty.tools.dotc.core.Phases._
import dotty.tools.dotc.core.Contexts._

class StainlessExtraction(inoxCtx: inox.InoxContext) extends Phase {

  def phaseName: String = "stainless extraction"

  def run(implicit ctx: Context): Unit = {
    val extraction = new CodeExtraction(inoxCtx)

    val unit = ctx.compilationUnit
    val tree = unit.tpdTree

    tree match {
      case pd @ PackageDef(_, _) =>
        val (pkg, allClasses, allFunctions) = extraction.extractPackage(pd)
        val syms = xlang.trees.NoSymbols.withClasses(allClasses).withFunctions(allFunctions)
        val program = new inox.Program {
          val trees = xlang.trees
          val ctx = inoxCtx
          val symbols = syms
        }

        println(pkg.asString(program.printerOpts))

      case _ =>
        println(tree)
    }
  }
}
