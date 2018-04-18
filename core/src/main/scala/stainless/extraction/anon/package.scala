/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

package object anon {

  object trees extends anon.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef]
    ) extends ClassSymbols with AbstractSymbols

    object printer extends Printer { val trees: anon.trees.type = anon.trees }
  }

  object extractor extends AnonymousClasses {
    val s: trees.type = trees
    val t: methods.trees.type = methods.trees
  }
}
