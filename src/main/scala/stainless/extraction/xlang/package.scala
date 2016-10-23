/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction

package object xlang {

  object trees extends xlang.Trees with oo.ObjectSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition],
      classes: Map[Identifier, ClassDef]
    ) extends ObjectSymbols with AbstractSymbols
  }

  /** As `xlang.Trees` don't extend the supported ASTs, the transformation from
    * these trees to `oo.Trees` simply consists in an identity mapping. */
  val extractor: inox.ast.SymbolTransformer {
    val s: trees.type
    val t: oo.trees.type
  } = inox.ast.SymbolTransformer(new ast.TreeTransformer {
    val s: trees.type = trees
    val t: oo.trees.type = oo.trees
  })
}
