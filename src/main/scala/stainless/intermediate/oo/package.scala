package stainless.intermediate

/**
  * Created by koukouto on 10/10/16.
  */
package object oo {

  object trees extends Trees with ObjectSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition],
      classes: Map[Identifier, ClassDef]
    ) extends ObjectSymbols
  }
}
