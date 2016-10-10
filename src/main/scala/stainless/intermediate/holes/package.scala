/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package intermediate

package object holes {

  object trees extends holes.Trees with inox.ast.SimpleSymbols {

    object deconstructor extends {
      protected val s: trees.type = trees
      protected val t: trees.type = trees
    } with holes.TreeDeconstructor

    override val NoSymbols = new Symbols(Map.empty, Map.empty)

    class Symbols(functions: Map[Identifier, FunDef], adts: Map[Identifier, ADTDefinition])
      extends super.Symbols(functions, adts)
        with AbstractSymbols
  }
}
