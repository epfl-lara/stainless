/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import extraction.xlang.{ trees => xt }
import utils.{ DependenciesFinder, Registry }

import scala.collection.mutable.{ ListBuffer }

/** Callback for verification */
class VerificationCallBack(val ctx: inox.Context) extends frontend.CallBack {

  // TODO Move Registry to frontend. Make a CallBackWithRegistery trait that uses the Registry.
  //      Re-use for TerminationCallBack.
  // implicit val debugSection = frontend.DebugSectionFrontend
  implicit val debugSection = DebugSectionVerification

  private val registry = new Registry {
    override val ctx = VerificationCallBack.this.ctx

    /** Compute the set of direct, non-recursive dependencies of the given [[xt.FunDef]] or [[xt.ClassDef]]. */
    override def computeDirectDependencies(fd: xt.FunDef): Set[Identifier] = new DependenciesFinder()(fd)
    override def computeDirectDependencies(cd: xt.ClassDef): Set[Identifier] = new DependenciesFinder()(cd)

    /** Checks whether the given function/class should be verified at some point. */
    // TODO this check should be moved to a utility package and copy/past code removed from stainless.
    override def shouldBeChecked(fd: xt.FunDef): Boolean = {
      val isLibrary = fd.flags contains "library"
      val isUnchecked = fd.flags contains "unchecked"
      !(isLibrary || isUnchecked)
      // TODO check --functions=... options for proper filter
    }

    // Invariants are already extracted to functions, so no need to process the class unless it's a dependency.
    override def shouldBeChecked(cd: xt.ClassDef): Boolean = false
  }

  override def beginExtractions(): Unit = { /* nothing */ }

  override def apply(file: String, unit: xt.UnitDef,
                     classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
    ctx.reporter.debug(s"Got a unit for $file: ${unit.id} with:") // Make this debug
    ctx.reporter.debug(s"\tfunctions -> [${functions.map { _.id }.sorted mkString ", "}]")
    ctx.reporter.debug(s"\tclasses   -> [${classes.map { _.id }.sorted mkString ", "}]")

    val symss = registry.update(classes, functions)
    processSymbols(symss)
  }

  override def endExtractions(): Unit = {
    val symss = registry.checkpoints()
    processSymbols(symss)
  }

  private def processSymbols(symss: Iterable[xt.Symbols]): Unit = symss foreach { syms =>
    // The registry tells us something should be verified in these symbols.
    val program = new inox.Program {
      val trees: extraction.xlang.trees.type = extraction.xlang.trees
      val ctx = VerificationCallBack.this.ctx
      val symbols = syms
    }

    try {
      syms.ensureWellFormed
    } catch {
      case e: syms.TypeErrorException =>
        ctx.reporter.error(e.pos, e.getMessage)
        ctx.reporter.error(s"The extracted sub-program in not well formed.")
        ctx.reporter.error(s"Symbols are:")
        ctx.reporter.error(s"functions -> [${syms.functions.keySet.toSeq.sorted mkString ", "}]")
        ctx.reporter.error(s"classes   -> [\n  ${syms.classes.values mkString "\n  "}]")
        ctx.reporter.fatalError(s"Aborting from VerificationCallBack")
    }

    ctx.reporter.debug(s"Solving program with ${syms.functions.size} functions & ${syms.classes.size} classes")

    solve(program)
  }

  private type Report = verification.VerificationComponent.Report
  private val tasks = ListBuffer[java.util.concurrent.Future[Report]]()

  private def solve(program: Program { val trees: extraction.xlang.trees.type }): Unit = {
    // Dispatch a task to the executor service instead of blocking this thread.
    val task = new java.util.concurrent.Callable[Report] {
      override def call(): Report = verification.VerificationComponent(program)
    }

    val future = MainHelpers.executor.submit(task)
    this.synchronized { tasks += future }
    // task.call() // For debug, comment the two previous lines and uncomment this one.
  }

  override def stop(): Unit = tasks foreach { _.cancel(true) }

  override def join(): Unit = tasks foreach { _.get }

  // See assumption/requirements in [[CallBack]]
  override def getReports = tasks map { _.get } filter { _ != null }

}

