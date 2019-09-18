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
    ExtractionPipeline(new CheckingTransformer {
      override val s: trees.type = trees
      override val t: imperative.trees.type = imperative.trees
    })
  }

    // utils.DebugPipeline("ExceptionLifting", ExceptionLifting(trees, imperative.trees))
}
