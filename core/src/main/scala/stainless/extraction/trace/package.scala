/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction

package object trace {

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

    object printer extends Printer { val trees: trace.trees.type = trace.trees }
  }

  def extractor(using inox.Context) = {
    utils.DebugPipeline("TraceInductElimination", TraceInductElimination(trees, termination.trees))
  }

  def fullExtractor(using inox.Context) = extractor andThen nextExtractor
  def nextExtractor(using inox.Context) = termination.fullExtractor

  def phaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: trace.trees.type } = {
    extraction.phaseSemantics(trace.trees)(fullExtractor)
  }

  def nextPhaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: termination.trees.type } = {
    termination.phaseSemantics
  }
}