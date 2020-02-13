/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

package object innerfuns {

  object trees extends Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols with AbstractSymbols

    object printer extends Printer { val trees: innerfuns.trees.type = innerfuns.trees }
  }

  def extractor(implicit ctx: inox.Context) = {
    utils.DebugPipeline("FunctionClosure", FunctionClosure(trees, inlining.trees))
  }

  def fullExtractor(implicit ctx: inox.Context) = extractor andThen nextExtractor
  def nextExtractor(implicit ctx: inox.Context) = inlining.fullExtractor

  def phaseSemantics(implicit ctx: inox.Context): inox.SemanticsProvider { val trees: innerfuns.trees.type } = {
    extraction.phaseSemantics(innerfuns.trees)(fullExtractor)
  }

  def nextPhaseSemantics(implicit ctx: inox.Context): inox.SemanticsProvider { val trees: inlining.trees.type } = {
    inlining.phaseSemantics
  }
}
