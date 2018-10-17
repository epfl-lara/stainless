/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package frontend

import scala.language.existentials

import extraction.xlang.{ TreeSanitizer, trees => xt }
import utils.{ CheckFilter, DependenciesFinder, JsonUtils, Registry }

import scala.collection.mutable.{ ListBuffer, Map => MutableMap, Set => MutableSet }

import io.circe._
import io.circe.syntax._

import java.io.File
import scala.concurrent.{ Await, Future }
import scala.concurrent.duration._

class StainlessCallBack(components: Seq[Component])(override implicit val context: inox.Context)
  extends CallBack with CheckFilter { self =>

  protected final override val trees = extraction.xlang.trees
  protected val pipeline: extraction.StainlessPipeline = extraction.pipeline

  import context.{ options, reporter }

  private[this] val runs = components.map(_.run(pipeline))

  private implicit val debugSection = DebugSectionFrontend

  /** Name of the sub-directory of [[optPersistentCache]] in which the registry cache files are saved. */
  protected val cacheSubDirectory: String = "stainless"

  /******************* Public Interface: Override CallBack ***************************************/

  final override def beginExtractions(): Unit = {
    assert(tasks.isEmpty)

    if (firstCycle) {
      loadCaches()
      firstCycle = false
    }
  }

  final override def apply(file: String, unit: xt.UnitDef,
                           classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
    reporter.debug(s"Got a unit for $file: ${unit.id} with:")
    reporter.debug(s"\tfunctions -> [${functions.map { _.id }.sorted mkString ", "}]")
    reporter.debug(s"\tclasses   -> [${classes.map { _.id }.sorted mkString ", "}]")

    // Update our state with the new data, producing new symbols through the registry.
    this.synchronized {
      recentIdentifiers ++= (classes map { _.id }) ++ (functions map { _.id })
      toProcess ++= functions map { _.id }
    }

    val symss = registry.update(classes, functions)
    processSymbols(symss)
  }

  final override def failed(): Unit = registry.failed()

  final override def endExtractions(): Unit = {
    val symss = registry.checkpoint()
    processSymbols(symss)

    if (report != null) report = report.filter(recentIdentifiers.toSet)
    recentIdentifiers.clear()
    toProcess.clear()
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

  protected trait RunReport { val run: ComponentRun; val report: run.component.Report }
  protected def RunReport(r: ComponentRun)(re: r.component.Report): RunReport { val run: r.type; val report: re.type } =
    new RunReport { val run: r.type = r; val report: re.type = re }

  protected case class Report(reports: Seq[RunReport]) extends AbstractReport[Report] {
    val name = "stainless"

    override def ~(other: Report): Report = Report(
      (reports ++ other.reports).groupBy(_.run).map {
        case (run, reports) => RunReport(run)(reports.map(_.report.asInstanceOf[run.component.Report]) reduce (_ ~ _))
      }.toSeq
    )

    override lazy val annotatedRows = reports.flatMap(_.report.annotatedRows: Seq[RecordRow])

    override def emitJson = reports.map(rr => rr.run.component.name -> rr.report.emitJson).asJson

    override def filter(ids: Set[Identifier]): Report =
      Report(reports.map(rr => RunReport(rr.run)(rr.report filter ids)))

    override lazy val stats: stainless.ReportStats = {
      val reportStats = reports.map(_.report.stats)
      ReportStats(
        reportStats.map(_.total         ).sum,
        reportStats.map(_.time          ).sum,
        reportStats.map(_.valid         ).sum,
        reportStats.map(_.validFromCache).sum,
        reportStats.map(_.invalid       ).sum,
        reportStats.map(_.unknown       ).sum)
    }
  }

  /** Parse a JSON value into a proper Report. We assume this doesn't fail. */
  protected def parseReportCache(json: Json): Report = json.as[Seq[(String, Json)]] match {
    case Right(jsons) => Report(runs.flatMap { run =>
      jsons.find(_._1 == run.component.name)
        .map(p => RunReport(run)(run.parse(p._2)): RunReport)
    })
    case Left(error) => throw error
  }

  // See assumption/requirements in [[CallBack]]
  final override def getReport: Option[Report] = Option(report)


  /******************* Internal State *************************************************************/

  private val tasks = ListBuffer[Future[Report]]()
  private var report: Report = _

  /** Set of classes/functions seen during the last callback cycle. */
  private val recentIdentifiers = MutableSet[Identifier]()

  /** Set of functions that still need to be processed. */
  private val toProcess = MutableSet[Identifier]()

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


  private def processSymbols(symss: Iterable[xt.Symbols]): Unit = {
    val ignoreFlags = Set("library", "synthetic")
    def shouldProcess(id: Identifier, syms: xt.Symbols): Boolean = {
      !syms.getFunction(id).flags.exists(f => ignoreFlags contains f.name) && this.synchronized {
        val res = toProcess(id)
        toProcess -= id
        res
      }
    }

    // The registry tells us something should be verified in these symbols.
    for (syms <- symss; id <- syms.functions.keys if shouldProcess(id, syms)) {
      val deps = syms.dependencies(id) + id
      val clsDeps = syms.classes.values.filter(cd => deps(cd.id)).toSeq
      val funDeps = syms.functions.values.filter(fd => deps(fd.id)).toSeq

      val funSyms = xt.NoSymbols.withClasses(clsDeps).withFunctions(funDeps)

      try {
        TreeSanitizer(xt).check(funSyms)
      } catch {
        case e: extraction.MissformedStainlessCode =>
          reportError(e.tree.getPos, e.getMessage, funSyms)
      }

      try {
        funSyms.ensureWellFormed
      } catch {
        case e: funSyms.TypeErrorException =>
          reportError(e.pos, e.getMessage, funSyms)
      }

      reporter.debug(s"Solving program with ${funSyms.functions.size} functions & ${funSyms.classes.size} classes")

      // Dispatch a task to the executor service instead of blocking this thread.
      val componentReports: Seq[Future[RunReport]] =
        runs.map(run => run(id, funSyms).map(a => RunReport(run)(a.toReport)))
      val futureReport = Future.sequence(componentReports).map(Report)
      this.synchronized { tasks += futureReport }
    }
  }

  private def reportError(pos: inox.utils.Position, msg: String, syms: xt.Symbols): Unit = {
    reporter.error(pos, msg)
    reporter.error(s"The extracted sub-program in not well formed.")
    reporter.error(s"Symbols are:")
    reporter.error(s"functions -> [${syms.functions.keySet.toSeq.sorted mkString ", "}]")
    reporter.error(s"classes   -> [\n  ${syms.classes.values mkString "\n  "}\n]")
    reporter.fatalError(s"Aborting from StainlessCallBack")
  }
}
