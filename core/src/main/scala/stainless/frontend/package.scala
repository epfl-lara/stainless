/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import stainless.extraction.xlang.{trees => xt}

package object frontend {

  /** An exception thrown when non-purescala compatible code is encountered. */
  sealed case class UnsupportedCodeException(pos: inox.utils.Position, msg: String)
    extends Exception(msg)

  object DebugSectionExtraction extends inox.DebugSection("extraction")

  object DebugSectionFrontend extends inox.DebugSection("frontend")

  object DebugSectionStack extends inox.DebugSection("stack")

  object DebugSectionCallGraph extends inox.DebugSection("call-graph")

  /** Do not use registry to create minimal partial programs,
    * do a dependency analysis after collecting the whole program
    */
  object optBatchedProgram extends inox.FlagOptionDef("batched", false)

  object optClasspath extends inox.OptionDef[Option[String]] {
    val name = "classpath"
    val default = None
    val parser = input => Some(Some(input))
    val usageRhs = "DIR"
  }

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
    factory(ctx, compilerArgs, getCallBack(using ctx))
  }

  /** All components handled by the frontend.  */
  val allComponents: Seq[Component] = Seq(
    verification.VerificationComponent,
    evaluators.EvaluatorComponent,
    genc.GenCComponent,
    testgen.ScalaTestGenComponent,
    testgen.GenCTestGenComponent,
    equivchk.EquivalenceCheckingComponent
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
  def getCallBack(using ctx: inox.Context): CallBack = {
    val activeComponents = getActiveComponents(ctx)
    if (batchSymbols(activeComponents))
      new BatchedCallBack(activeComponents)
    else {
      if (ctx.reporter.isDebugEnabled(using DebugSectionCallGraph)) {
        ctx.reporter.fatalError("--debug=callgraph may only be used with --batched")
      }
      new SplitCallBack(activeComponents)
    }
  }

  private def batchSymbols(activeComponents: Seq[Component])(using ctx: inox.Context): Boolean = {
    ctx.options.findOptionOrDefault(optBatchedProgram) ||
    activeComponents.exists(Set(genc.GenCComponent, testgen.ScalaTestGenComponent, testgen.GenCTestGenComponent).contains) ||
    ctx.options.findOptionOrDefault(optKeep).nonEmpty
  }


  // removes the `StrictBV` flag used in `CodeExtraction`
  val strictBVCleaner = extraction.oo.SymbolTransformer(new BVCleanerImpl(xt, xt))

  class BVCleanerImpl(override val s: xt.type, override val t: xt.type) extends transformers.ConcreteTreeTransformer(s, t) {
    override def transform(tpe: xt.Type): xt.Type = tpe match {
      case xt.AnnotatedType(tp, flags) if flags.exists(_ != xt.StrictBV) =>
        xt.AnnotatedType(transform(tp), flags.filter(_ != xt.StrictBV))
      case xt.AnnotatedType(tp, flags) =>
        transform(tp)
      case _ =>
        super.transform(tpe)
    }
  }
}

