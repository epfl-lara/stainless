/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction

package object inlining {

  object trees extends Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols with StainlessAbstractSymbols {
      override val symbols: this.type = this
    }

    override def mkSymbols(functions: Map[Identifier, FunDef], sorts: Map[Identifier, ADTSort]): Symbols = {
      Symbols(functions, sorts)
    }

    object printer extends Printer { val trees: inlining.trees.type = inlining.trees }
  }

  def extractor(using inox.Context) = {
    utils.NamedPipeline("FunctionSpecialization", FunctionSpecialization(trees)) andThen
    utils.NamedPipeline("UnfoldOpaque", UnfoldOpaque(trees)) andThen
    utils.NamedPipeline("CallSiteInline", CallSiteInline(trees)) andThen
    utils.NamedPipeline("ChooseInjector", ChooseInjector(trees)) andThen
    utils.NamedPipeline("ChooseEncoder", ChooseEncoder(trees, trees)) andThen
    utils.NamedPipeline("FunctionInlining", FunctionInlining(trees, trace.trees))
  }

  def fullExtractor(using inox.Context) = extractor andThen nextExtractor
  def nextExtractor(using inox.Context) = trace.fullExtractor

  def phaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: inlining.trees.type } = {
    extraction.phaseSemantics(inlining.trees)(fullExtractor)
  }

  def nextPhaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: trace.trees.type } = {
    trace.phaseSemantics
  }
}
