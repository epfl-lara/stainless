/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

package object termination {

  type TerminationProgram = Program { val trees: termination.trees.type }

  object trees extends termination.Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition]
    ) extends SimpleSymbols with AbstractSymbols
  }
}
