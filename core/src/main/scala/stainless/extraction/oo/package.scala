/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction

package object oo {

  object trees extends Trees with ObjectSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition],
      classes: Map[Identifier, ClassDef]
    ) extends ObjectSymbols
  }

  object extractor extends MethodLifting {
    val s: trees.type = trees
    val t: holes.trees.type = holes.trees
  }
}
