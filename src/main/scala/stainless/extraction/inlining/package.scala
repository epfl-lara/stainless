/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction

package object inlining {
  
  object trees extends Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition]
    ) extends SimpleSymbols with AbstractSymbols
  }

  object extractor extends FunctionInlining {
    val s: trees.type = trees
    val t: extraction.trees.type = extraction.trees
  }
}
