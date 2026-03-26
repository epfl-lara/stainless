/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction

package object skolems {

  object trees extends skolems.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef],
      typeDefs: Map[Identifier, TypeDef],
    ) extends ClassSymbols with InnerClassesAbstractSymbols {
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

    object printer extends skolems.Printer {
      val trees: skolems.trees.type = skolems.trees
    }
  }

  def extractor(using inox.Context) = {
    class ExtractorImpl(override val s: trees.type, override val t: xlang.trees.type) extends CheckingTransformer

    val extraction = ExtractionPipeline(new ExtractorImpl(trees, xlang.trees))
    utils.NamedPipeline("SkolemLifting", SkolemLifting(trees, xlang.trees))

  }

  def fullExtractor(using inox.Context) = extractor `andThen` nextExtractor
  def nextExtractor(using inox.Context) = xlang.fullExtractor

  def phaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: skolems.trees.type } = {
    extraction.phaseSemantics(skolems.trees)(fullExtractor)
  }

  def nextPhaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: xlang.trees.type } = {
    xlang.phaseSemantics
  }
}
