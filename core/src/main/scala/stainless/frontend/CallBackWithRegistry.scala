/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontend

import extraction.xlang.{ trees => xt }
import utils.{ DependenciesFinder, Registry }

import scala.collection.mutable.{ ListBuffer, Map => MutableMap }

import java.io.{ File, PrintWriter }
import java.util.Scanner

import org.json4s._
import org.json4s.native.JsonMethods._

trait CallBackWithRegistry extends CallBack { self =>
  import context.{ options, reporter }

  private implicit val debugSection = DebugSectionFrontend

  /******************* Public Interface: Override CallBack ***************************************/

  final override def beginExtractions(): Unit = {
    assert(tasks.isEmpty)

    if (firstCycle) {
      loadCaches()
      firstCycle = false
    }

    onCycleBegin()
  }

  final override def apply(file: String, unit: xt.UnitDef,
                           classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
    reporter.debug(s"Got a unit for $file: ${unit.id} with:")
    reporter.debug(s"\tfunctions -> [${functions.map { _.id }.sorted mkString ", "}]")
    reporter.debug(s"\tclasses   -> [${classes.map { _.id }.sorted mkString ", "}]")

    // Remove any node from the registry that no longer exists.
    previousFileData get file foreach { case (prevClasses, prevFuns) =>
      val removedClasses = prevClasses filterNot { cd => classes exists { _.id == cd.id } }
      val removedClassesIds = removedClasses map { _.id }
      val removedFuns = prevFuns filterNot { cd => functions exists { _.id == cd.id } }
      val removedFunsIds = removedFuns map { _.id }

      reporter.debug(s"Removing the following from the registry:")
      reporter.debug(s"\tfunctions -> [${removedFunsIds.sorted mkString ", "}]")
      reporter.debug(s"\tclasses   -> [${removedClassesIds.sorted mkString ", "}]")

      registry.remove(removedClasses, removedFuns)
      if (report != null) report = report.removeSubreports(removedClassesIds ++ removedFunsIds)
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

  final override def stop(): Unit = tasks foreach { _.cancel(true) } // no need to update state, it's a KILL.

  // Build the report
  final override def join(): Unit = {
    val newReports = tasks map { _.get } // blocking! TODO is there a more efficient "get all" version?
    val reports = (report +: newReports) filter { _ != null }
    if (reports.nonEmpty) {
      report = reports reduce { _ ~ _ }
    }
    tasks.clear()

    // Save cache now that we have our report
    saveCaches()
  }

  // See assumption/requirements in [[CallBack]]
  final override def getReport: Option[Report] = Some(report) filter { _ != null }


  /******************* Customisation Points *******************************************************/

  protected val context: inox.Context

  protected type Report <: AbstractReport[Report]

  /** Reset state for a new cycle. */
  protected def onCycleBegin(): Unit

  /** Produce a report for the given program, in a blocking fashion. */
  protected def solve(program: Program { val trees: extraction.xlang.trees.type }): Report

  /** Checks whether the given function/class should be processed at some point. */
  protected def shouldBeChecked(fd: xt.FunDef): Boolean
  protected def shouldBeChecked(cd: xt.ClassDef): Boolean

  /** Name of the sub-directory of [[optPersistentCache]] in which the registry cache files are saved. */
  protected val cacheSubDirectory: String

  /** Parse a JSON value into a proper Report. We assume this doesn't fail. */
  protected def parseReportCache(json: JValue): Report


  /******************* Internal State *************************************************************/

  private val tasks = ListBuffer[java.util.concurrent.Future[Report]]()
  private var report: Report = _

  private val previousFileData = MutableMap[String, (Seq[xt.ClassDef], Seq[xt.FunDef])]()

  private val registry = new Registry {
    override val context = self.context

    override def computeDirectDependencies(fd: xt.FunDef): Set[Identifier] = new DependenciesFinder()(fd)
    override def computeDirectDependencies(cd: xt.ClassDef): Set[Identifier] = new DependenciesFinder()(cd)

    override def shouldBeChecked(fd: xt.FunDef): Boolean = self.shouldBeChecked(fd)
    override def shouldBeChecked(cd: xt.ClassDef): Boolean = self.shouldBeChecked(cd)
  }

  private var firstCycle = true // used to trigger cache loading the first time.


  /******************* Internal Helpers ***********************************************************/

  private def getCacheFile(filename: String): Option[File] =
    utils.Caches.getCacheFile(context, optPersistentRegistryCache, cacheSubDirectory, filename)

  private def getRegistryCacheFile: Option[File] = getCacheFile("registry.bin")
  private def getReportCacheFile: Option[File] = getCacheFile("report.json")

  case class CacheFiles(registry: File, report: File)
  private def getCacheFiles: Option[CacheFiles] = (getRegistryCacheFile, getReportCacheFile) match {
    case (None, None) => None
    case (Some(registry), Some(report)) => Some(CacheFiles(registry, report))
    case _ => reporter.internalError(s"inconsistent state") // either both are off, or both are on.
  }

  /** Load the registry & report caches, if specified by the user and available. */
  private def loadCaches(): Unit = getCacheFiles foreach { caches =>
    reporter.debug(s"Loading registry & report caches from ${caches.registry.getParent}")

    if (caches.registry.isFile != caches.report.isFile) {
      reporter.error(s"Inconsistent cache state, ignoring cache from ${caches.registry.getParent}")
    } else if (caches.registry.isFile()) {
      // Load registry cache
      registry.loadCache(caches.registry)

      // Load report cache
      val sc = new Scanner(caches.report)
      val sb = new StringBuilder
      while (sc.hasNextLine) { sb ++= sc.nextLine + "\n" }
      val json = parse(sb.toString)
      report = parseReportCache(json)
    }
  }

  /** Save the registry & report caches, if specified by the user. */
  private def saveCaches(): Unit = if (report != null) getCacheFiles foreach { caches =>
    reporter.debug(s"Saving registry & report caches to ${caches.registry.getParent}")

    registry.saveCache(caches.registry)

    val json = report.emitJson
    val string = compact(render(json))
    val pw = new PrintWriter(caches.report)
    try pw.write(string) finally pw.close()
  }


  private def processSymbols(symss: Iterable[xt.Symbols]): Unit = symss foreach { syms =>
    // The registry tells us something should be verified in these symbols.
    val program = inox.Program(extraction.xlang.trees)(syms)

    try {
      syms.ensureWellFormed
    } catch {
      case e: syms.TypeErrorException =>
        reporter.error(e.pos, e.getMessage)
        reporter.error(s"The extracted sub-program in not well formed.")
        reporter.error(s"Symbols are:")
        reporter.error(s"functions -> [${syms.functions.keySet.toSeq.sorted mkString ", "}]")
        reporter.error(s"classes   -> [\n  ${syms.classes.values mkString "\n  "}\n]")
        reporter.fatalError(s"Aborting from CallBackWithRegistry")
    }

    reporter.debug(s"Solving program with ${syms.functions.size} functions & ${syms.classes.size} classes")

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

