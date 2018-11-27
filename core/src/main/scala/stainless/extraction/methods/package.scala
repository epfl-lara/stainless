/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

package object methods {

  object trees extends methods.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef]
    ) extends ClassSymbols with AbstractSymbols

    object printer extends Printer { val trees: methods.trees.type = methods.trees }
  }

  class MethodsException(tree: inox.ast.Trees#Tree, msg: String)
    extends MalformedStainlessCode(tree, msg)

  object MethodsException {
    def apply(tree: inox.ast.Trees#Tree, msg: String) = new MethodsException(tree, msg)
  }

  def extractor(implicit ctx: inox.Context) =
    utils.DebugPipeline("Laws", Laws(trees)) andThen
    utils.DebugPipeline("SuperCalls", SuperCalls(trees)) andThen
    utils.DebugPipeline("Sealing", Sealing(trees)) andThen
    utils.DebugPipeline("MethodLifting", MethodLifting(trees, trees)) andThen
    utils.DebugPipeline("FieldAccessors", FieldAccessors(trees, throwing.trees))
}
