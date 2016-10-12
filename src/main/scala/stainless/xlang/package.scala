/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import inox.ast.Identifier

package object xlang {

  object trees extends xlang.Trees with intermediate.oo.ObjectSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition],
      classes: Map[Identifier, ClassDef]
    ) extends ObjectSymbols with AbstractSymbols
  }
}
