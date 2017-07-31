/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontend

import scala.collection.mutable.{ ListBuffer, Map => MutableMap }

import extraction.xlang.{ trees => xt }
import utils.{ DependenciesFinder, Registry }

/**
 * Process the extracted units.
 *
 * Frontends are required to follow this workflow:
 *  - when starting extracting compilation unit, [[beginExtractions]] should be called once;
 *  - the [[CallBack.apply]] method after extracting each compilation unit (i.e. a Scala file);
 *  - finally, the frontend calls [[endExtractions]] to let the CallBack know all the data
 *    should be available by now.
 *
 * When a compilation unit is recompiled, the callback deals with any potential invalidation of
 * existing data without blocking the callee's thread.
 *
 * A [[Frontend]] has to [[stop]] or [[join]] its callback at some point.
 *
 * Calling [[getReports]] is valid if and only if:
 *  - the callback has been joined, and
 *  - the program was not running in "watch" mode.
 *
 * NOTE A callback is expected to be used by only one frontend at a time.
 */
trait CallBack {
  def beginExtractions(): Unit
  def apply(file: String, unit: xt.UnitDef, classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit
  def endExtractions(): Unit

  def stop(): Unit // Blocking "stop".

  def join(): Unit // Wait until all tasks have finished.

  def getReports: Seq[AbstractReport]
}


/** MasterCallBack: combine several callbacks together. */
final class MasterCallBack(val callbacks: Seq[CallBack]) extends CallBack {
  override def beginExtractions(): Unit = callbacks foreach { _.beginExtractions() }

  override def apply(file: String, unit: xt.UnitDef,
                     classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
    callbacks foreach { c => c(file, unit, classes, functions) }
  }

  override def endExtractions(): Unit = callbacks foreach { _.endExtractions() }

  override def stop(): Unit = callbacks foreach { _.stop() }

  override def join(): Unit = callbacks foreach { _.join() }

  // Group together reports from the same callback
  override def getReports: Seq[AbstractReport] = callbacks flatMap { c =>
    val inners = c.getReports
    if (inners.isEmpty) None
    else Some(inners reduce { _ ~ _ })
  }
}


trait CallBackWithRegistry extends CallBack { self =>

  /******************* Public Interface: Override CallBack ***************************************/

  final override def beginExtractions(): Unit = { /* nothing */ }

  final override def apply(file: String, unit: xt.UnitDef,
                           classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
    ctx.reporter.debug(s"Got a unit for $file: ${unit.id} with:")
    ctx.reporter.debug(s"\tfunctions -> [${functions.map { _.id }.sorted mkString ", "}]")
    ctx.reporter.debug(s"\tclasses   -> [${classes.map { _.id }.sorted mkString ", "}]")

    // Remove any node from the registry that no longer exists.
    previousFileData get file foreach { case (prevClasses, prevFuns) =>
      val removedClasses = prevClasses filterNot { cd => classes exists { _.id == cd.id } }
      val removedFuns = prevFuns filterNot { cd => functions exists { _.id == cd.id } }
      ctx.reporter.debug(s"Removing the following from the registry:")
      ctx.reporter.debug(s"\tfunctions -> [${removedFuns.map { _.id }.sorted mkString ", "}]")
      ctx.reporter.debug(s"\tclasses   -> [${removedClasses.map { _.id }.sorted mkString ", "}]")
      registry.remove(removedClasses, removedFuns)
    }

    // Update our state with the new data, producing new symbols through the registry.
    previousFileData += file -> (classes, functions)
    val symss = registry.update(classes, functions)
    processSymbols(symss)
  }

  final override def endExtractions(): Unit = {
    val symss = registry.checkpoints()
    processSymbols(symss)
  }

  final override def stop(): Unit = tasks foreach { _.cancel(true) }

  final override def join(): Unit = tasks foreach { _.get }

  // See assumption/requirements in [[CallBack]]
  final override def getReports: Seq[Report] = tasks map { _.get } filter { _ != null }


  /******************* Customisation Points *******************************************************/

  protected type Report <: AbstractReport

  protected val ctx: inox.Context

  /** Produce a report for the given program, in a blocking fashion. */
  protected def solve(program: Program { val trees: extraction.xlang.trees.type }): Report

  /** Checks whether the given function/class should be processed at some point. */
  protected def shouldBeChecked(fd: xt.FunDef): Boolean
  protected def shouldBeChecked(cd: xt.ClassDef): Boolean


  /******************* Internal State *************************************************************/

  private implicit val debugSection = DebugSectionFrontend
  private val tasks = ListBuffer[java.util.concurrent.Future[Report]]()

  private val previousFileData = MutableMap[String, (Seq[xt.ClassDef], Seq[xt.FunDef])]()

  private val registry = new Registry {
    override val ctx = self.ctx

    override def computeDirectDependencies(fd: xt.FunDef): Set[Identifier] = new DependenciesFinder()(fd)
    override def computeDirectDependencies(cd: xt.ClassDef): Set[Identifier] = new DependenciesFinder()(cd)

    override def shouldBeChecked(fd: xt.FunDef): Boolean = self.shouldBeChecked(fd)
    override def shouldBeChecked(cd: xt.ClassDef): Boolean = self.shouldBeChecked(cd)
  }


  /******************* Internal Helpers ***********************************************************/

  private def processSymbols(symss: Iterable[xt.Symbols]): Unit = symss foreach { syms =>
    // The registry tells us something should be verified in these symbols.
    val program = new inox.Program {
      val trees: extraction.xlang.trees.type = extraction.xlang.trees
      val ctx = self.ctx
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
        ctx.reporter.error(s"classes   -> [\n  ${syms.classes.values mkString "\n  "}\n]")
        ctx.reporter.fatalError(s"Aborting from CallBackWithRegistry")
    }

    ctx.reporter.debug(s"Solving program with ${syms.functions.size} functions & ${syms.classes.size} classes")

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

