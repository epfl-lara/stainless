/* Copyright 2009-2018 EPFL, Lausanne */

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

  def extractor(implicit ctx: inox.Context) = 
    utils.DebugPipeline("FunctionInlining", FunctionInlining(trees, extraction.trees))
}
