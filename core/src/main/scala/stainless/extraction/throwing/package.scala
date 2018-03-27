/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

package object throwing {

  object trees extends throwing.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef]
    ) extends ClassSymbols

    object printer extends Printer { val trees: throwing.trees.type = throwing.trees }
  }

  object extractor extends ExceptionLifting {
    val s: trees.type = trees
    val t: oo.trees.type = oo.trees
  }
}
