/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction

package object methods {

  object trees extends methods.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef],
      typeDefs: Map[Identifier, TypeDef],
    ) extends ClassSymbols with MethodsAbstractSymbols {
      override val symbols: this.type = this
    }

    override def mkSymbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef],
      typeDefs: Map[Identifier, TypeDef],
    ): Symbols = {
      Symbols(functions, sorts, classes, typeDefs)
    }

    object printer extends Printer { val trees: methods.trees.type = methods.trees }
  }

  class MethodsException(tree: inox.ast.Trees#Tree, msg: String)
    extends MalformedStainlessCode(tree, msg)

  object MethodsException {
    def apply(tree: inox.ast.Trees#Tree, msg: String) = new MethodsException(tree, msg)
  }

  def lowering(using inox.Context) = {
    class LoweringImpl(override val s: trees.type, override val t: throwing.trees.type) extends CheckingTransformer
    ExtractionPipeline(new LoweringImpl(trees, throwing.trees))
  }

  def extractor(using inox.Context) = {
    utils.NamedPipeline("Laws",            Laws(trees))            `andThen`
    utils.NamedPipeline("SuperInvariants", SuperInvariants(trees)) `andThen`
    utils.NamedPipeline("SuperCalls",      SuperCalls(trees))      `andThen`
    utils.NamedPipeline("Sealing",         Sealing(trees))         `andThen`
    utils.NamedPipeline("MethodLifting",   MethodLifting(trees))   `andThen`
    utils.NamedPipeline("MergeInvariants", MergeInvariants(trees)) `andThen`
    utils.NamedPipeline("FieldAccessors",  FieldAccessors(trees))  `andThen`
    utils.NamedPipeline("ValueClasses",    ValueClasses(trees))    `andThen`
    utils.NamedPipeline("MethodsLowering", lowering)
  }

  def fullExtractor(using inox.Context) = extractor `andThen` nextExtractor
  def nextExtractor(using inox.Context) = throwing.fullExtractor

  def phaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: methods.trees.type } = {
    extraction.phaseSemantics(methods.trees)(fullExtractor)
  }

  def nextPhaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: throwing.trees.type } = {
    throwing.phaseSemantics
  }
}
