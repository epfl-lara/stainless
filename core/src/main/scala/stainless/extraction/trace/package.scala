/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

package object trace {

  object trees extends Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols with AbstractSymbols

    object printer extends Printer { val trees: trace.trees.type = trace.trees }
  }

  def extractor(implicit ctx: inox.Context) = {
    utils.DebugPipeline("Trace", Trace(trees, termination.trees))
  }

  def fullExtractor(implicit ctx: inox.Context) = extractor andThen nextExtractor
  def nextExtractor(implicit ctx: inox.Context) = termination.fullExtractor

  def phaseSemantics(implicit ctx: inox.Context): inox.SemanticsProvider { val trees: trace.trees.type } = {
    extraction.phaseSemantics(trace.trees)(fullExtractor)
  }

  def nextPhaseSemantics(implicit ctx: inox.Context): inox.SemanticsProvider { val trees: termination.trees.type } = {
    termination.phaseSemantics
  }
}