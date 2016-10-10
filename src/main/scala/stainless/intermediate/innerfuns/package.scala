/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package intermediate

package object innerfuns {
  
  object trees extends innerfuns.Trees with inox.ast.SimpleSymbols {

    object deconstructor extends {
      protected val s: trees.type = trees
      protected val t: trees.type = trees
    } with innerfuns.TreeDeconstructor

    override val NoSymbols = new Symbols(Map.empty, Map.empty)

    class Symbols(functions: Map[Identifier, FunDef], adts: Map[Identifier, ADTDefinition])
      extends super.Symbols(functions, adts)
        with AbstractSymbols
  }
}
