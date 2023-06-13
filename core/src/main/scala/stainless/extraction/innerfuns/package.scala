/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction

package object innerfuns {

  object trees extends Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols with InnerFunsAbstractSymbols {
      override val symbols: this.type = this
    }

    override def mkSymbols(functions: Map[Identifier, FunDef], sorts: Map[Identifier, ADTSort]): Symbols = {
      Symbols(functions, sorts)
    }

    object printer extends Printer { val trees: innerfuns.trees.type = innerfuns.trees }
  }

  def extractor(using inox.Context) = {
    utils.NamedPipeline("FunctionClosure", FunctionClosure(trees, inlining.trees))
  }

  def fullExtractor(using inox.Context) = extractor andThen nextExtractor
  def nextExtractor(using inox.Context) = inlining.fullExtractor

  def phaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: innerfuns.trees.type } = {
    extraction.phaseSemantics(innerfuns.trees)(fullExtractor)
  }

  def nextPhaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: inlining.trees.type } = {
    inlining.phaseSemantics
  }
}
