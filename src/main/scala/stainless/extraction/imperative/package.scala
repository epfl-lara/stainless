/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package extraction

package object imperative {

  object trees extends imperative.Trees with inox.ast.SimpleSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      adts: Map[Identifier, ADTDefinition]
    ) extends SimpleSymbols with AbstractSymbols
  }

  object globalState extends {
    val s: trees.type = trees
    val t: trees.type = trees
  } with GlobalStateIntroduction

  object antiAliasing extends {
    val s: trees.type = trees
    val t: trees.type = trees
  } with AntiAliasing

  object imperativeElimination extends {
    val s: trees.type = trees
    val t: trees.type = trees
  } with ImperativeCodeElimination

  object cleanup extends {
    val s: trees.type = trees
    val t: innerfuns.trees.type = innerfuns.trees
  } with ImperativeCleanup

  val extractor = globalState andThen antiAliasing andThen imperativeElimination andThen cleanup
}
