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

  def extractor(implicit ctx: inox.Context) = {
    val lowering = ExtractionPipeline(new CheckingTransformer {
      override val s: trees.type = trees
      override val t: imperative.trees.type = imperative.trees
    })

    import utils.PositionChecker

    AdtSpecialization(trees, trees) andThen
    RefinementLifting(trees, trees) andThen
    TypeEncoding(trees, trees)      andThen
    lowering
  }
}
