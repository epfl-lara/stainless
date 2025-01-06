/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction

package object imperative {

  object optFullImperative extends inox.FlagOptionDef("full-imperative", false)

  object trees extends imperative.Trees with oo.ClassSymbols {
    case class Symbols(
      functions: Map[Identifier, FunDef],
      sorts: Map[Identifier, ADTSort],
      classes: Map[Identifier, ClassDef],
      typeDefs: Map[Identifier, TypeDef],
    ) extends ClassSymbols with ImperativeAbstractSymbols {
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

    object printer extends Printer { val trees: imperative.trees.type = imperative.trees }
  }

  class ImperativeEliminationException(tree: inox.ast.Trees#Tree, msg: String)
    extends MalformedStainlessCode(tree, msg)

  object ImperativeEliminationException {
    def apply(tree: inox.ast.Trees#Tree, msg: String) = new ImperativeEliminationException(tree, msg)
  }

  /**
    * This pipeline enforces non-aliasing of mutable state
    */
  def defaultImperative(using inox.Context) = {
    utils.NamedPipeline("EffectElaboration", EffectElaboration(trees)).andThen(  // only drops definitions
    utils.NamedPipeline("AntiAliasing", AntiAliasing(trees)).andThen(
    utils.NamedPipeline("ReturnElimination", ReturnElimination(trees)).andThen(
    utils.NamedPipeline("ImperativeCodeElimination", ImperativeCodeElimination(trees)).andThen(
    utils.NamedPipeline("ImperativeCleanup", ImperativeCleanup(trees, oo.trees))))))
  }

  /**
    * This pipeline uses dynamic frames to handle shared mutable state
    * 
    * "Generalized Arrays for Stainless Frames" VMCAI 2022
    * https://link.springer.com/chapter/10.1007/978-3-030-94583-1_17
    */
  def fullImperative(using inox.Context) = {
    utils.NamedPipeline("EffectElaboration", EffectElaboration(trees)).andThen(
    utils.NamedPipeline("ImperativeCodeElimination", ImperativeCodeElimination(trees)).andThen(
    utils.NamedPipeline("ImperativeCleanup", ImperativeCleanup(trees, oo.trees))))
  }

  def extractor(using ctx: inox.Context) =
    if (ctx.options.findOptionOrDefault(optFullImperative)) fullImperative
    else defaultImperative

  def fullExtractor(using inox.Context) = extractor `andThen` nextExtractor
  def nextExtractor(using inox.Context) = oo.fullExtractor

  def phaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: imperative.trees.type } = {
    extraction.phaseSemantics(imperative.trees)(fullExtractor)
  }

  def nextPhaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: oo.trees.type } = {
    oo.phaseSemantics
  }
}
