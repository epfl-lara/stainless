/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

package object inlining {

  object trees extends Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols with AbstractSymbols

    object printer extends Printer { val trees: inlining.trees.type = inlining.trees }
  }

  def extractor(implicit ctx: inox.Context) = {
    utils.DebugPipeline("FunctionSpecialization", FunctionSpecialization(trees)) andThen
    utils.DebugPipeline("CallSiteInline", CallSiteInline(trees)) andThen
    utils.DebugPipeline("ChooseInjector", ChooseInjector(trees)) andThen
    utils.DebugPipeline("ChooseEncoder", ChooseEncoder(trees)) andThen
    utils.DebugPipeline("FunctionInlining", FunctionInlining(trees, trace.trees))
  }

  def fullExtractor(implicit ctx: inox.Context) = extractor andThen nextExtractor
  def nextExtractor(implicit ctx: inox.Context) = trace.fullExtractor

  def phaseSemantics(implicit ctx: inox.Context): inox.SemanticsProvider { val trees: inlining.trees.type } = {
    extraction.phaseSemantics(inlining.trees)(fullExtractor)
  }

  def nextPhaseSemantics(implicit ctx: inox.Context): inox.SemanticsProvider { val trees: trace.trees.type } = {
    trace.phaseSemantics
  }
}
