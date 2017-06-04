/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

package object oo {

  object trees extends Trees with ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition],
      classes: Map[Identifier, ClassDef]
    ) extends ClassSymbols

    object printer extends Printer { val trees: oo.trees.type = oo.trees }
  }

  object methods extends MethodLifting {
    val s: trees.type = trees
    val t: trees.type = trees
  }

  object adts extends AdtSpecialization {
    val s: trees.type = trees
    val t: trees.type = trees
  }

  object encoding extends TypeEncoding {
    val s: trees.type = trees
    val t: holes.trees.type = holes.trees
  }

  val extractor = methods andThen adts andThen encoding

}
