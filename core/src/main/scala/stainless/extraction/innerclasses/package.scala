/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction

package object innerclasses {

  object trees extends innerclasses.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef],
      typeDefs: Map[Identifier, TypeDef],
    ) extends ClassSymbols with InnerClassesAbstractSymbols {
      override val symbols: this.type = this
    }

    override def mkSymbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef],
      typeDefs: Map[Identifier, TypeDef],
    ): Symbols = {
      Symbols(functions, sorts, classes, typeDefs)
    }

    object printer extends Printer { val trees: innerclasses.trees.type = innerclasses.trees }
  }

  class InvalidInnerClassException(tree: inox.ast.Trees#Tree, msg: String)
    extends MalformedStainlessCode(tree, msg)

  object InvalidInnerClassException {
    def apply(tree: inox.ast.Trees#Tree, msg: String) = new InvalidInnerClassException(tree, msg)
  }

  def extractor(using inox.Context) = {
    utils.DebugPipeline("InnerClasses", InnerClasses(trees, methods.trees))
  }

  def fullExtractor(using inox.Context) = extractor andThen nextExtractor
  def nextExtractor(using inox.Context) = methods.fullExtractor

  def phaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: innerclasses.trees.type } = {
    extraction.phaseSemantics(innerclasses.trees)(fullExtractor)
  }

  def nextPhaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: methods.trees.type } = {
    methods.phaseSemantics
  }
}
