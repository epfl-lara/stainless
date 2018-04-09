/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package frontend

import extraction.xlang.{ trees => xt }
import utils.{ CheckFilter, DependenciesFinder, JsonUtils, Registry }

import scala.collection.mutable.{ ListBuffer, Map => MutableMap, Set => MutableSet }

import io.circe.Json

import java.io.File
import scala.concurrent.{ Await, Future }
import scala.concurrent.duration._

trait CallBackWithRegistry extends CallBack with CheckFilter { self =>
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

    // Update our state with the new data, producing new symbols through the registry.
    recentIdentifiers ++= (classes map { _.id }) ++ (functions map { _.id })
    val symss = registry.update(classes, functions)
    processSymbols(symss)
  }

  final override def failed(): Unit = registry.failed()

  final override def endExtractions(): Unit = {
    val symss = registry.checkpoint()
    processSymbols(symss)

    if (report != null) report = report.filter(recentIdentifiers.toSet)
    recentIdentifiers.clear()
  }

  final override def stop(): Unit = {
    tasks foreach { Await.result(_, 1.seconds) } // no need to update state, it's a KILL.
    tasks.clear()
  }

  // Build the report
  final override def join(): Unit = try {
    val newReports = Await.result(Future.sequence(tasks), Duration.Inf)
    val reports = (report +: newReports) filter { _ != null }
    if (reports.nonEmpty) report = reports reduce { _ ~ _ }
    tasks.clear()

    // Save cache now that we have our report
    saveCaches()
  } catch {
    case SomeFatalError(e) =>
      stop()
      throw e
  }

  object SomeFatalError {
    def unapply(ex: Throwable): Option[Throwable] = ex match {
      case e: inox.FatalError => Some(e)
      case e if e.getCause != null => SomeFatalError.unapply(e.getCause)
      case _ => None
    }
  }

  // See assumption/requirements in [[CallBack]]
  final override def getReport: Option[Report] = Option(report)


  /******************* Customisation Points *******************************************************/

  protected implicit val context: inox.Context

  protected type Report <: AbstractReport[Report]

  /** Reset state for a new cycle. */
  protected def onCycleBegin(): Unit

  /** Produce a report for the given program, in a blocking fashion. */
  protected def solve(program: Program { val trees: xt.type }): Future[Report]

  protected final override val trees = xt // not customisable as not needed.

  /** Name of the sub-directory of [[optPersistentCache]] in which the registry cache files are saved. */
  protected val cacheSubDirectory: String

  /** Parse a JSON value into a proper Report. We assume this doesn't fail. */
  protected def parseReportCache(json: Json): Report


  /******************* Internal State *************************************************************/

  private val tasks = ListBuffer[Future[Report]]()
  private var report: Report = _

  /** Set of classes/functions seen during the last callback cycle. */
  private val recentIdentifiers = MutableSet[Identifier]()

  private val registry = new Registry {
    override val context = self.context

    override def computeDirectDependencies(fd: xt.FunDef): Set[Identifier] = new DependenciesFinder()(fd)
    override def computeDirectDependencies(cd: xt.ClassDef): Set[Identifier] = new DependenciesFinder()(cd)

    override def shouldBeChecked(fd: xt.FunDef): Boolean = self.shouldBeChecked(fd)
  }

  private var firstCycle = true // used to trigger cache loading the first time.


  /******************* Internal Helpers ***********************************************************/

  private def getCacheFile(filename: String): Option[File] =
    utils.Caches.getCacheFile(context, optPersistentCache, cacheSubDirectory, filename)

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
      val json = JsonUtils.parseFile(caches.report)
      report = parseReportCache(json)
    }
  }

  /** Save the registry & report caches, if specified by the user. */
  private def saveCaches(): Unit = if (report != null) getCacheFiles foreach { caches =>
    reporter.debug(s"Saving registry & report caches to ${caches.registry.getParent}")

    registry.saveCache(caches.registry)

    val json = report.emitJson
    JsonUtils.writeFile(caches.report, json)
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

  private def processProgram(program: Program { val trees: xt.type }): Unit = {
    // Dispatch a task to the executor service instead of blocking this thread.
    this.synchronized { tasks += solve(program) }
  }

}

