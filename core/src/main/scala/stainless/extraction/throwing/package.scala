/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction

package object throwing {

  object trees extends throwing.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef],
      typeDefs: Map[Identifier, TypeDef],
    ) extends ClassSymbols with ImperativeAbstractSymbols {
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

    object printer extends Printer {
      val trees: throwing.trees.type = throwing.trees
    }
  }

  def extractor(using inox.Context) = {
    class ExtractorImpl(override val s: trees.type, override val t: imperative.trees.type) extends CheckingTransformer
    // utils.DebugPipeline("ExceptionLifting", ExceptionLifting(trees, imperative.trees))
    ExtractionPipeline(new ExtractorImpl(trees, imperative.trees))
  }

  def fullExtractor(using inox.Context) = extractor andThen nextExtractor
  def nextExtractor(using inox.Context) = imperative.fullExtractor

  def phaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: throwing.trees.type } = {
    extraction.phaseSemantics(throwing.trees)(fullExtractor)
  }

  def nextPhaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: imperative.trees.type } = {
    imperative.phaseSemantics
  }
}
