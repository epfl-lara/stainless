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

  def oldImperative(using inox.Context) = {
    utils.DebugPipeline("EffectElaboration", EffectElaboration(trees)) andThen  // only drops definitions
    utils.DebugPipeline("AntiAliasing", AntiAliasing(trees)) andThen
    utils.DebugPipeline("ReturnElimination", ReturnElimination(trees)) andThen
    utils.DebugPipeline("ImperativeCodeElimination", ImperativeCodeElimination(trees)) andThen
    utils.DebugPipeline("ImperativeCleanup", ImperativeCleanup(trees, oo.trees))
  }

  def newImperative(using inox.Context) = {
    utils.DebugPipeline("EffectElaboration", EffectElaboration(trees)) andThen
    utils.DebugPipeline("ImperativeCodeElimination", ImperativeCodeElimination(trees)) andThen
    utils.DebugPipeline("ImperativeCleanup", ImperativeCleanup(trees, oo.trees))
  }

  def extractor(using ctx: inox.Context) =
    if (ctx.options.findOptionOrDefault(optFullImperative)) newImperative
    else oldImperative

  def fullExtractor(using inox.Context) = extractor andThen nextExtractor
  def nextExtractor(using inox.Context) = oo.fullExtractor

  def phaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: imperative.trees.type } = {
    extraction.phaseSemantics(imperative.trees)(fullExtractor)
  }

  def nextPhaseSemantics(using inox.Context): inox.SemanticsProvider { val trees: oo.trees.type } = {
    oo.phaseSemantics
  }
}
