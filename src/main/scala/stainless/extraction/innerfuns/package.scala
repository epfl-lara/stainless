/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction

package object innerfuns {
  
  object trees extends Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition]
    ) extends SimpleSymbols with AbstractSymbols
  }

  // FIXME: This transformer will crash if it encounters an AST from `innerfuns.Trees`.
  //        This is a temporary place-holder until innerfuns extraction has been ported from Leon.
  val extractor: inox.ast.SymbolTransformer {
    val s: trees.type
    val t: extraction.trees.type
  } = inox.ast.SymbolTransformer(new ast.TreeTransformer {
    val s: trees.type = trees
    val t: extraction.trees.type = extraction.trees
  })
}
