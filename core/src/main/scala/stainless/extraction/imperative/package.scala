/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

package object imperative {

  object trees extends imperative.Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols with AbstractSymbols

    object printer extends Printer { val trees: imperative.trees.type = imperative.trees }
  }

  class ImperativeEliminationException(tree: inox.ast.Trees#Tree, msg: String)
    extends MissformedStainlessCode(tree, msg)

  object ImperativeEliminationException {
    def apply(tree: inox.ast.Trees#Tree, msg: String) = new ImperativeEliminationException(tree, msg)
  }

  def extractor(implicit ctx: inox.Context) =
    utils.DebugPipeline("imperative.AntiAliasing", AntiAliasing(trees)) andThen
    utils.DebugPipeline("imperative.ImperativeCodeElimination", ImperativeCodeElimination(trees)) andThen
    utils.DebugPipeline("imperative.ImperativeCleanup", ImperativeCleanup(trees, innerfuns.trees))
}
