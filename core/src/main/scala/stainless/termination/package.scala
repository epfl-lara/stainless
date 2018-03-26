/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

package object termination {

  type TerminationProgram = Program { val trees: termination.trees.type }

  object trees extends termination.Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort]
    ) extends SimpleSymbols with AbstractSymbols

    object printer extends Printer { val trees: termination.trees.type = termination.trees }
  }
}
