/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

package object oo {

  object trees extends oo.Trees with ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef]
    ) extends ClassSymbols

    object printer extends Printer { val trees: oo.trees.type = oo.trees }
  }

  val adts = PipelineBuilder(trees, trees)(AdtSpecialization(trees, trees))
  val refinements = PipelineBuilder(trees, trees)(RefinementLifting(trees, trees))
  val encoding = PipelineBuilder(trees, imperative.trees)(TypeEncoding(trees, imperative.trees))

  val extractor = adts andThen refinements andThen encoding
}
