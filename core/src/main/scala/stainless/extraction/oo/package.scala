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

  object adts extends AdtSpecialization {
    val s: trees.type = trees
    val t: trees.type = trees
  }

  object refinements extends RefinementLifting {
    val s: trees.type = trees
    val t: trees.type = trees
  }

  object encoding extends TypeEncoding {
    val s: trees.type = trees
    val t: trees.type = trees
  }

  val checker = inox.ast.SymbolTransformer(new CheckingTransformer {
    val s: trees.type = trees
    val t: holes.trees.type = holes.trees
  })

  val extractor = adts andThen refinements andThen encoding andThen checker
}
