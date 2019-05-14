/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

package object throwing {

  object trees extends throwing.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef]
    ) extends ClassSymbols with AbstractSymbols

    object printer extends Printer { val trees: throwing.trees.type = throwing.trees }
  }

  def extractor(implicit ctx: inox.Context) = 
    utils.DebugPipeline("ExceptionLifting", ExceptionLifting(trees, imperative.trees))
}
