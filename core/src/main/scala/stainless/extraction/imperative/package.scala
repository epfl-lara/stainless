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

  case class ImperativeEliminationException(pos: inox.utils.Position, msg: String) extends Exception(msg)

  object antiAliasing extends {
    val trees: imperative.trees.type = imperative.trees
  } with AntiAliasing

  object imperativeElimination extends {
    val trees: imperative.trees.type = imperative.trees
  } with ImperativeCodeElimination

  object cleanup extends {
    val s: trees.type = trees
    val t: innerfuns.trees.type = innerfuns.trees
  } with ImperativeCleanup

  val extractor = antiAliasing andThen imperativeElimination andThen cleanup
}
