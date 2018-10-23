/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package extraction

import scala.language.existentials

package object innerclasses {

  object trees extends innerclasses.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef]
    ) extends ClassSymbols with AbstractSymbols

    object printer extends Printer { val trees: innerclasses.trees.type = innerclasses.trees }
  }

  class InvalidInnerClassException(tree: inox.ast.Trees#Tree, msg: String)
    extends MissformedStainlessCode(tree, msg)

  object InvalidInnerClassException {
    def apply(tree: inox.ast.Trees#Tree, msg: String) = new InvalidInnerClassException(tree, msg)
  }

  def extractor(implicit ctx: inox.Context) = {
    val lowering = ExtractionPipeline(new CheckingTransformer {
      override val s: trees.type = trees
      override val t: methods.trees.type = methods.trees
    })

    utils.DebugPipeline("InnerClasses", InnerClasses(trees)) andThen lowering
  }
}
