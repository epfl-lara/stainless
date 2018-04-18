/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

package object innerclasses {

  object trees extends innerclasses.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef]
    ) extends ClassSymbols with AbstractSymbols

    object printer extends Printer { val trees: innerclasses.trees.type = innerclasses.trees }
  }

  object extractor extends InnerClasses {
    val s: trees.type = trees
    val t: methods.trees.type = methods.trees
  }
}
