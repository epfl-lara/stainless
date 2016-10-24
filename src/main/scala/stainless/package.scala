/* Copyright 2009-2016 EPFL, Lausanne */

package object stainless {

  type Program = inox.Program { val trees: ast.Trees }

  type StainlessProgram = Program { val trees: stainless.trees.type }

  /** Including these aliases here makes default imports more natural. */
  type Identifier = inox.Identifier
  val FreshIdentifier = inox.FreshIdentifier

  object trees extends ast.Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition]
    ) extends SimpleSymbols with AbstractSymbols
  }
}
