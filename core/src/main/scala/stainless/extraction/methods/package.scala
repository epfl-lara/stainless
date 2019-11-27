/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

package object methods {

  object trees extends methods.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef],
      typeDefs: Map[Identifier, TypeDef],
    ) extends ClassSymbols with AbstractSymbols

    object printer extends Printer { val trees: methods.trees.type = methods.trees }
  }

  class MethodsException(tree: inox.ast.Trees#Tree, msg: String)
    extends MalformedStainlessCode(tree, msg)

  object MethodsException {
    def apply(tree: inox.ast.Trees#Tree, msg: String) = new MethodsException(tree, msg)
  }

  def extractor(implicit ctx: inox.Context) = {
    val lowering = ExtractionPipeline(new CheckingTransformer {
      override val s: trees.type = trees
      override val t: throwing.trees.type = throwing.trees
    })

    utils.DebugPipeline("Laws",            Laws(trees))            andThen
    utils.DebugPipeline("SuperInvariants", SuperInvariants(trees))      andThen
    utils.DebugPipeline("SuperCalls",      SuperCalls(trees))      andThen
    utils.DebugPipeline("Sealing",         Sealing(trees))         andThen
    utils.DebugPipeline("MethodLifting",   MethodLifting(trees))   andThen
    utils.DebugPipeline("MergeInvariants", MergeInvariants(trees)) andThen
    utils.DebugPipeline("FieldAccessors",  FieldAccessors(trees))  andThen
    utils.DebugPipeline("ValueClasses",    ValueClasses(trees))    andThen
    lowering
  }

  def fullExtractor(implicit ctx: inox.Context) = extractor andThen nextExtractor
  def nextExtractor(implicit ctx: inox.Context) = throwing.fullExtractor

  def phaseSemantics(implicit ctx: inox.Context): inox.SemanticsProvider { val trees: methods.trees.type } = {
    extraction.phaseSemantics(methods.trees)(fullExtractor)
  }

  def nextPhaseSemantics(implicit ctx: inox.Context): inox.SemanticsProvider { val trees: throwing.trees.type } = {
    throwing.phaseSemantics
  }
}
