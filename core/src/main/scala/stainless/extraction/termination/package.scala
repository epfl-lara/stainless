/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

package object termination {

  object optTermination extends inox.FlagOptionDef("termination", true)

  object DebugSectionTermination extends inox.DebugSection("termination")

  object trees extends Trees with inox.ast.SimpleSymbols {
    case class Symbols(
        functions: Map[Identifier, FunDef],
        sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols
        with AbstractSymbols

    object printer extends Printer { val trees: termination.trees.type = termination.trees }
  }

  case class FailedMeasureInference(fd: inox.ast.Trees#FunDef, msg: String)
    extends Exception(msg)

  def extractor(implicit ctx: inox.Context) = {
    val lowering = ExtractionPipeline(new CheckingTransformer {
      override val s: trees.type = trees
      override val t: extraction.trees.type = extraction.trees
    })

    utils.DebugPipeline("SizedADTExtraction", SizedADTExtraction(trees)) andThen
    utils.DebugPipeline("InductElimination", InductElimination(trees)) andThen
    // utils.DebugPipeline("SizeInjection", SizeInjection(trees)) andThen
    utils.DebugPipeline("MeasureAnnotation", MeasureAnnotation(trees)) andThen
    lowering
  }

  def fullExtractor(implicit ctx: inox.Context) = extractor

  def phaseSemantics(
      implicit ctx: inox.Context
  ): inox.SemanticsProvider { val trees: termination.trees.type } = {
    extraction.phaseSemantics(termination.trees)(fullExtractor)
  }

  def nextPhaseSemantics(
      implicit ctx: inox.Context
  ): inox.SemanticsProvider { val trees: extraction.trees.type } = {
    extraction.extractionSemantics
  }
}
