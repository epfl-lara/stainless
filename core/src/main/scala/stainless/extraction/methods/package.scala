/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

package object methods {

  object trees extends methods.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef]
    ) extends ClassSymbols with AbstractSymbols

    object printer extends Printer { val trees: methods.trees.type = methods.trees }
  }

  def extractor(implicit ctx: inox.Context) = MethodLifting(trees, throwing.trees)
}
