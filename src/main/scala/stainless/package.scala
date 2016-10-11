/* Copyright 2009-2016 EPFL, Lausanne */

package object stainless {

  type StainlessProgram = inox.Program { val trees: stainless.trees.type }

  object trees extends ast.Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition]
    ) extends SimpleSymbols with AbstractSymbols
  }
}
