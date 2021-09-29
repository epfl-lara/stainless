/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

package object termination {

  object trees extends Trees with inox.ast.SimpleSymbols {
    case class Symbols(
        functions: Map[Identifier, FunDef],
        sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols
        with AbstractSymbols

    object printer extends Printer { val trees: termination.trees.type = termination.trees }
  }

  def extractor(implicit ctx: inox.Context) = {
    val lowering = ExtractionPipeline(new CheckingTransformer {
      override val s: trees.type = trees
      override val t: extraction.trees.type = extraction.trees

      // We remove `Induct` flags that may appear in let bindings and in variables after FunctionInlining
      override def transform(vd: s.ValDef): t.ValDef = {
        t.ValDef(vd.id, transform(vd.tpe), vd.flags.filter(_ != s.Induct).map(transform)).copiedFrom(vd)
      }

      override def transform(e: s.Expr): t.Expr = e match {
        case s.Variable(id, tpe, flags) =>
          t.Variable(id, transform(tpe), flags.filter(_ != s.Induct).map(transform)).copiedFrom(e)
        case _ => super.transform(e)
      }
    })

    utils.DebugPipeline("SizedADTExtraction", SizedADTExtraction(trees)) andThen
    utils.DebugPipeline("InductElimination", InductElimination(trees)) andThen
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
