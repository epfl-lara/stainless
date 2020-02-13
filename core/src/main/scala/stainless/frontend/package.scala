/* Copyright 2009-2019 EPFL, Lausanne */

package stainless

package object frontend {

  /** An exception thrown when non-purescala compatible code is encountered. */
  sealed case class UnsupportedCodeException(pos: inox.utils.Position, msg: String)
    extends Exception(msg)

  object DebugSectionExtraction extends inox.DebugSection("extraction")

  object DebugSectionFrontend extends inox.DebugSection("frontend")

  /**
   * The persistent caches are stored in the same directory, denoted by this option.
   */
  object optPersistentCache extends inox.FlagOptionDef("cache", false)

  /** Do not use registry to create minimal partial programs,
    * do a dependency analysis after collecting the whole program
    */
  object optBatchedProgram extends inox.FlagOptionDef("batched", false)

  /**
   * Given a context (with its reporter) and a frontend factory, proceed to compile,
   * extract, transform and verify the input programs based on the active components
   * when [[run]] is invoked on the returned frontend.
   *
   * The returned frontend is allowed to run forever in the background, e.g. when
   * watching for file changes. This function is therefore non-blocking. The callee
   * is required to [[stop]] or [[join]] the returned compiler to free resources.
   */
  def build(ctx: inox.Context, compilerArgs: Seq[String], factory: FrontendFactory): Frontend = {
    factory(ctx, compilerArgs, getCallBack(ctx))
  }

  /** All components handled by the frontend.  */
  val allComponents: Seq[Component] = Seq(
    verification.VerificationComponent,
    evaluators.EvaluatorComponent
  )

  /**
   * Based on the context option, return the list of active component (e.g. verification, termination).
   * By default, return [[stainless.verification.VerificationComponent]].
   */
  private def getActiveComponents(ctx: inox.Context): Seq[Component] = {
    val fromOptions = allComponents.filter { c =>
      ctx.options.options.collectFirst {
        case inox.OptionValue(o, value: Boolean) if o.name == c.name => value
      }.getOrElse(false)
    }

    if (fromOptions.isEmpty) {
      Seq(verification.VerificationComponent)
    } else {
      fromOptions
    }
  }

  /** Get one callback for all active components. */
  def getCallBack(implicit ctx: inox.Context): CallBack = {
    val activeComponents = getActiveComponents(ctx)
    if (batchSymbols(activeComponents))
      new BatchedCallBack(activeComponents)
    else
      new SplitCallBack(activeComponents)
  }

  private def batchSymbols(activeComponents: Seq[Component])(implicit ctx: inox.Context): Boolean = {
    ctx.options.findOptionOrDefault(optBatchedProgram) ||
    !ctx.options.findOptionOrDefault(optKeep).isEmpty
  }
}

