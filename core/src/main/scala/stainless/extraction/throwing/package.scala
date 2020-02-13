/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

package object throwing {

  object trees extends throwing.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef],
      typeDefs: Map[Identifier, TypeDef],
    ) extends ClassSymbols with AbstractSymbols

    object printer extends Printer {
      val trees: throwing.trees.type = throwing.trees
    }
  }

  def extractor(implicit ctx: inox.Context) = {
    // utils.DebugPipeline("ExceptionLifting", ExceptionLifting(trees, imperative.trees))
    ExtractionPipeline(new CheckingTransformer {
      override val s: trees.type = trees
      override val t: imperative.trees.type = imperative.trees
    })
  }

  def fullExtractor(implicit ctx: inox.Context) = extractor andThen nextExtractor
  def nextExtractor(implicit ctx: inox.Context) = imperative.fullExtractor

  def phaseSemantics(implicit ctx: inox.Context): inox.SemanticsProvider { val trees: throwing.trees.type } = {
    extraction.phaseSemantics(throwing.trees)(fullExtractor)
  }

  def nextPhaseSemantics(implicit ctx: inox.Context): inox.SemanticsProvider { val trees: imperative.trees.type } = {
    imperative.phaseSemantics
  }
}
