/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

package object frontend {

  object DebugSectionFrontend extends inox.DebugSection("frontend")

  /**
   * Given a context (with its reporter) and a compiler factory, proceed to compile,
   * extract, transform and verify the input programs based on the active components.
   *
   * The returned compiler is allowed to run forever in the background, e.g. when
   * watching for file changes. This function is therefore non-blocking. The callee
   * is required to [[stop]] or [[join]] the returned compiler to free resources.
   */
  def run(ctx: inox.Context, compilerArgs: Seq[String], factory: FrontendFactory): Frontend = {
    val callback = getCallBackForActiveComponents(ctx)

    // Initiate & run the compiler for our needs.
    val compiler = factory(ctx, compilerArgs, callback)
    compiler.run()

    compiler
  }

  /**
   * All components handled by the frontend.
   *
   * TODO It might be interesting to be able to add at runtime more components.
   *
   * NOTE [[database]] and [[components]] need to be kept in sync.
   */
  val allComponents: Seq[Component] = Seq(
    verification.VerificationComponent,
    termination.TerminationComponent
  )

  /** CallBack factories for each component. */
  private val database = Map[String, inox.Context => CallBack](
    verification.VerificationComponent.name -> { ctx => new verification.VerificationCallBack(ctx) },
    termination.TerminationComponent.name -> { ctx => new termination.TerminationCallBack(ctx) }
  )

  private def getCallBack(name: String, ctx: inox.Context): CallBack = database(name)(ctx)

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
  private def getCallBackForActiveComponents(ctx: inox.Context): CallBack = {
    val activeComponents = getActiveComponents(ctx)
    val activeCallbacks = activeComponents map { c => getCallBack(c.name, ctx) }

    // Distribute events to active components:
    new MasterCallBack(activeCallbacks)
  }

}

