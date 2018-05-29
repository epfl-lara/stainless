/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

package object frontend {

  /** An exception thrown when non-purescala compatible code is encountered. */
  sealed case class UnsupportedCodeException(val pos: inox.utils.Position, msg: String)
    extends Exception(msg)

  object DebugSectionFrontend extends inox.DebugSection("frontend")

  /**
   * The persistent caches are stored in the same directory, denoted by this option.
   */
  object optPersistentCache extends inox.FlagOptionDef("cache", false)

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
    factory(ctx, compilerArgs, getStainlessCallBack(ctx))
  }

  /**
   * All components handled by the frontend.
   *
   * NOTE [[database]] and [[components]] need to be kept in sync.
   */
  val allComponents: Seq[Component] = Seq(
    verification.VerificationComponent,
    termination.TerminationComponent,
    evaluators.EvaluatorComponent
  )

  /**
   * Based on the context option, return the list of active component (e.g. verification, termination).
   * By default, return [[stainless.verification.VerificationComponent]].
   */
  private def getActiveComponents(ctx: inox.Context) = {
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
  def getStainlessCallBack(implicit ctx: inox.Context): CallBack = {
    val activeComponents = getActiveComponents(ctx)
    new StainlessCallBack(activeComponents)
  }
}

