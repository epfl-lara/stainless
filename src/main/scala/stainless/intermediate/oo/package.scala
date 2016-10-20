/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package intermediate

package object oo {

  object trees extends Trees with ObjectSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition],
      classes: Map[Identifier, ClassDef]
    ) extends ObjectSymbols
  }
}
