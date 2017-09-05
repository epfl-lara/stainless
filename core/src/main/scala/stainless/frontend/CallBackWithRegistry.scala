/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontend

import extraction.xlang.{ trees => xt }
import utils.{ DependenciesFinder, Registry }

import scala.collection.mutable.{ ListBuffer, Map => MutableMap }

trait CallBackWithRegistry extends CallBack { self =>
  protected val context: inox.Context

  private implicit val debugSection = DebugSectionFrontend

  /******************* Public Interface: Override CallBack ***************************************/

  override def beginExtractions(): Unit = { /* nothing */ }

  final override def apply(file: String, unit: xt.UnitDef,
                           classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
    context.reporter.debug(s"Got a unit for $file: ${unit.id} with:")
    context.reporter.debug(s"\tfunctions -> [${functions.map { _.id }.sorted mkString ", "}]")
    context.reporter.debug(s"\tclasses   -> [${classes.map { _.id }.sorted mkString ", "}]")

    // Remove any node from the registry that no longer exists.
    previousFileData get file foreach { case (prevClasses, prevFuns) =>
      val removedClasses = prevClasses filterNot { cd => classes exists { _.id == cd.id } }
      val removedFuns = prevFuns filterNot { cd => functions exists { _.id == cd.id } }
      context.reporter.debug(s"Removing the following from the registry:")
      context.reporter.debug(s"\tfunctions -> [${removedFuns.map { _.id }.sorted mkString ", "}]")
      context.reporter.debug(s"\tclasses   -> [${removedClasses.map { _.id }.sorted mkString ", "}]")
      registry.remove(removedClasses, removedFuns)
    }

    // Update our state with the new data, producing new symbols through the registry.
    previousFileData += file -> (classes, functions)
    val symss = registry.update(classes, functions)
    processSymbols(symss)
  }

  final override def endExtractions(): Unit = {
    val symss = registry.checkpoint()
    processSymbols(symss)
  }

  final override def stop(): Unit = tasks foreach { _.cancel(true) }

  final override def join(): Unit = tasks foreach { _.get }

  // See assumption/requirements in [[CallBack]]
  final override def getReports: Seq[Report] = tasks map { _.get } filter { _ != null }


  /******************* Customisation Points *******************************************************/

  protected type Report <: AbstractReport

  /** Produce a report for the given program, in a blocking fashion. */
  protected def solve(program: Program { val trees: extraction.xlang.trees.type }): Report

  /** Checks whether the given function/class should be processed at some point. */
  protected def shouldBeChecked(fd: xt.FunDef): Boolean
  protected def shouldBeChecked(cd: xt.ClassDef): Boolean


  /******************* Internal State *************************************************************/

  private val tasks = ListBuffer[java.util.concurrent.Future[Report]]()

  private val previousFileData = MutableMap[String, (Seq[xt.ClassDef], Seq[xt.FunDef])]()

  private val registry = new Registry {
    override val context = self.context

    override def computeDirectDependencies(fd: xt.FunDef): Set[Identifier] = new DependenciesFinder()(fd)
    override def computeDirectDependencies(cd: xt.ClassDef): Set[Identifier] = new DependenciesFinder()(cd)

    override def shouldBeChecked(fd: xt.FunDef): Boolean = self.shouldBeChecked(fd)
    override def shouldBeChecked(cd: xt.ClassDef): Boolean = self.shouldBeChecked(cd)
  }


  /******************* Internal Helpers ***********************************************************/

  private def processSymbols(symss: Iterable[xt.Symbols]): Unit = symss foreach { syms =>
    // The registry tells us something should be verified in these symbols.
    val program = inox.Program(extraction.xlang.trees)(syms)

    try {
      syms.ensureWellFormed
    } catch {
      case e: syms.TypeErrorException =>
        context.reporter.error(e.pos, e.getMessage)
        context.reporter.error(s"The extracted sub-program in not well formed.")
        context.reporter.error(s"Symbols are:")
        context.reporter.error(s"functions -> [${syms.functions.keySet.toSeq.sorted mkString ", "}]")
        context.reporter.error(s"classes   -> [\n  ${syms.classes.values mkString "\n  "}\n]")
        context.reporter.fatalError(s"Aborting from CallBackWithRegistry")
    }

    context.reporter.debug(s"Solving program with ${syms.functions.size} functions & ${syms.classes.size} classes")

    processProgram(program)
  }

  private def processProgram(program: Program { val trees: extraction.xlang.trees.type }): Unit = {
    // Dispatch a task to the executor service instead of blocking this thread.
    val task = new java.util.concurrent.Callable[Report] {
      override def call(): Report = solve(program)
    }

    val future = MainHelpers.executor.submit(task)
    this.synchronized { tasks += future }
    // task.call() // For debug, comment the two previous lines and uncomment this one.
  }

}
