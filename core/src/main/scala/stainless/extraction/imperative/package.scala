/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

package object imperative {

  object trees extends imperative.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef]
    ) extends ClassSymbols with AbstractSymbols

    object printer extends Printer { val trees: imperative.trees.type = imperative.trees }
  }

  class ImperativeEliminationException(tree: inox.ast.Trees#Tree, msg: String)
    extends MissformedStainlessCode(tree, msg)

  object ImperativeEliminationException {
    def apply(tree: inox.ast.Trees#Tree, msg: String) = new ImperativeEliminationException(tree, msg)
  }

  def extractor(implicit ctx: inox.Context) =
    utils.DebugPipeline("AntiAliasing", AntiAliasing(trees)) andThen
    utils.DebugPipeline("ImperativeCodeElimination", ImperativeCodeElimination(trees)) andThen
    utils.DebugPipeline("ImperativeCleanup", ImperativeCleanup(trees, oo.trees))
}
