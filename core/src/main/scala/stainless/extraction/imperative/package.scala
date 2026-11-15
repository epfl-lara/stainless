/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package extraction

package object imperative {

  object optFullImperative extends inox.FlagOptionDef("full-imperative", false)

  object optImperativeV2 extends inox.FlagOptionDef("imperative-v2", false)

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

  class AliasingRewriteException(tree: inox.ast.Trees#Tree, msg: String)
    extends MalformedStainlessCode(tree, msg)

  object AliasingRewriteException {
    def apply(tree: inox.ast.Trees#Tree, msg: String) = new AliasingRewriteException(tree, msg)

    private val capturedMutationMessage =
      "a lambda or local function mutates an object it captured from its enclosing function -- its enclosing aliases cannot be refreshed"

    def capturedMutation(tree: inox.ast.Trees#Tree) = apply(tree, capturedMutationMessage)

    private val innerAliasMessage =
      "an object inside this call's argument is also reachable from outside the argument -- the callee may mutate or replace it, so its outside aliases cannot be refreshed definitely"

    def innerAlias(tree: inox.ast.Trees#Tree) = apply(tree, innerAliasMessage)

    private val nonFreshResultMessage =
      "this recursive function or lambda returns a result that shares a mutable object within itself -- AssignmentRewrite treats its calls as opaque and assumes their results are fresh"

    def nonFreshResult(tree: inox.ast.Trees#Tree) = apply(tree, nonFreshResultMessage)

    private val reassignedCopyMessage =
      "this recursive function or lambda reassigns the local copy of a mutable parameter -- its effect on the parameter cannot be written back"

    def reassignedCopy(tree: inox.ast.Trees#Tree) = apply(tree, reassignedCopyMessage)

    private val nonFreshDefaultMessage =
      "the default value of `Array.fill` must be fresh -- every position would hold the same object"

    def nonFreshDefault(tree: inox.ast.Trees#Tree) = apply(tree, nonFreshDefaultMessage)

    private val sharedCollectionMessage =
      "a collection and its copy are both used after the copy -- they share their mutable elements"

    def sharedCollection(tree: inox.ast.Trees#Tree) = apply(tree, sharedCollectionMessage)

    private val danglingIndexMessage =
      "this collection element is indexed by a variable that goes out of scope while the element is still reachable"

    def danglingIndex(tree: inox.ast.Trees#Tree) = apply(tree, danglingIndexMessage)

    private val unimportableCallMessage =
      "the effect of this call cannot be expressed at the call site"

    def unimportableCall(tree: inox.ast.Trees#Tree) = apply(tree, unimportableCallMessage)

    private val effectfulIndexedCallMessage =
      "an argument of this call has side effects, while a collection element passed to it is indexed by a value that may change -- " +
      "bind the arguments to variables before the call"

    def effectfulIndexedCall(tree: inox.ast.Trees#Tree) = apply(tree, effectfulIndexedCallMessage)

    private val opaqueWriteMessage =
      "this recursive function or lambda writes a reference into an object it did not create -- " +
      "AssignmentRewrite treats its calls as opaque and cannot import such an effect"

    def opaqueWrite(tree: inox.ast.Trees#Tree) = apply(tree, opaqueWriteMessage)

    private val opaqueEffectMessage =
      "this recursive function or lambda returns an object reachable from its parameters, or writes a reference into them -- " +
      "AssignmentRewrite treats its calls as opaque and cannot import such an effect"

    def opaqueEffect(tree: inox.ast.Trees#Tree) = apply(tree, opaqueEffectMessage)

    private val unknownVariableMessage =
      "a refresh targets a variable that is not declared in the function body -- " +
      "this indicates a gap in AssignmentRewrite's analysis"

    def unknownVariable(tree: inox.ast.Trees#Tree) = apply(tree, unknownVariableMessage)

    private val unrebuildableValueMessage =
      "a refresh needs to rebuild a value whose type is neither a class nor a tuple"

    def unrebuildableValue(tree: inox.ast.Trees#Tree) = apply(tree, unrebuildableValueMessage)

    private val unknownFieldOwnerMessage =
      "a refresh writes a field whose owning class could not be found"

    def unknownFieldOwner(tree: inox.ast.Trees#Tree) = apply(tree, unknownFieldOwnerMessage)

    private val unsupportedConstructMessage =
      "this construct is not yet supported by AssignmentRewrite's heap analysis"

    def unsupportedConstruct(tree: inox.ast.Trees#Tree) = apply(tree, s"$unsupportedConstructMessage: ${tree.getClass.getSimpleName}")

    private val ambiguousAliasMessage =
      "this mutation may or may not affect another live alias (it depends on a branch, a loop " +
      "iteration, or which object the receiver denotes), so AssignmentRewrite cannot refresh it definitely"

    def ambiguousAlias(tree: inox.ast.Trees#Tree) = apply(tree, ambiguousAliasMessage)

    private val staleCaptureMessage =
      "this lambda captures a variable that is reassigned or refreshed in the function -- after imperative elimination the lambda would see a stale value"

    def staleCapture(tree: inox.ast.Trees#Tree) = apply(tree, staleCaptureMessage)

    private val nonConvergentLoopMessage =
      "the heap analysis did not stabilize on this loop -- loops that walk a recursive structure (e.g. `l = l.tail`) are not yet supported by AssignmentRewrite's heap analysis"

    def nonConvergentLoop(tree: inox.ast.Trees#Tree) = apply(tree, nonConvergentLoopMessage)

    private val conditionOutOfScopeMessage =
      "this mutation affects an alias only under a branch condition that is no longer in scope here " +
      "(e.g. the condition of an `if` nested in another branch), so AssignmentRewrite cannot refresh it"

    def conditionOutOfScope(tree: inox.ast.Trees#Tree) = apply(tree, conditionOutOfScopeMessage)

    private val keyOutOfScopeMessage =
      "this mutation affects an alias stored in a collection under an index or key that is no longer in scope here, " +
      "so AssignmentRewrite cannot refresh it"

    def keyOutOfScope(tree: inox.ast.Trees#Tree) = apply(tree, keyOutOfScopeMessage)

    private val mutableInstantiationMessage =
      "a type parameter that is not @mutable is instantiated with a mutable type -- its mutable contents cannot be tracked"

    def mutableInstantiation(tree: inox.ast.Trees#Tree) = apply(tree, mutableInstantiationMessage)

    private val sharedArgumentMessage =
      "an object is reachable through two different paths of this call's arguments -- the callee assumes they are distinct"

    def sharedArgument(tree: inox.ast.Trees#Tree) = apply(tree, sharedArgumentMessage)

  }

  /**
    * This pipeline enforces non-aliasing of mutable state
    */
  def defaultImperative(using inox.Context) = {
    utils.NamedPipeline("SameAsLowering", SameAsLowering(trees)).andThen(
    utils.NamedPipeline("EffectElaboration", EffectElaboration(trees)).andThen(  // only drops definitions
    utils.NamedPipeline("AntiAliasing", AntiAliasing(trees)).andThen(
    utils.NamedPipeline("ReturnElimination", ReturnElimination(trees)).andThen(
    utils.NamedPipeline("ImperativeCodeElimination", ImperativeCodeElimination(trees)).andThen(
    utils.NamedPipeline("ImperativeCleanup", ImperativeCleanup(trees, oo.trees)))))))
  }

  /**
    * This pipeline uses dynamic frames to handle shared mutable state
    *
    * "Generalized Arrays for Stainless Frames" VMCAI 2022
    * https://link.springer.com/chapter/10.1007/978-3-030-94583-1_17
    */
  def fullImperative(using inox.Context) = {
    utils.NamedPipeline("SameAsLowering", SameAsLowering(trees)).andThen(
    utils.NamedPipeline("EffectElaboration", EffectElaboration(trees)).andThen(
    utils.NamedPipeline("ImperativeCodeElimination", ImperativeCodeElimination(trees)).andThen(
    utils.NamedPipeline("ImperativeCleanup", ImperativeCleanup(trees, oo.trees)))))
  }

  def imperativeV2(using inox.Context) = {
    utils.NamedPipeline("SameAsLowering", SameAsLowering(trees)).andThen(
    utils.NamedPipeline("EffectElaboration", EffectElaboration(trees)).andThen(
    utils.NamedPipeline("FunctionRewrite", FunctionRewrite(trees)).andThen(
    utils.NamedPipeline("ConditionalHoisting", ConditionalHoisting(trees)).andThen(
    utils.NamedPipeline("AssignmentRewrite", AssignmentRewrite(trees)).andThen(
    utils.NamedPipeline("ReturnElimination", ReturnElimination(trees)).andThen(
    utils.NamedPipeline("ImperativeCodeElimination", ImperativeCodeElimination(trees)).andThen(
    utils.NamedPipeline("ImperativeCleanup", ImperativeCleanup(trees, oo.trees)))))))))
  }

  def extractor(using ctx: inox.Context) =
    if (ctx.options.findOptionOrDefault(optFullImperative)) fullImperative
    else if (ctx.options.findOptionOrDefault(optImperativeV2)) imperativeV2
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
