/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package frontend

import stainless.utils.LibraryFilter

import scala.language.existentials

import extraction.xlang.{ TreeSanitizer, trees => xt }
import extraction.utils.ConcurrentCache
import utils.{ CheckFilter, JsonUtils }

import scala.collection.mutable.{ ListBuffer, Set => MutableSet }

import io.circe._
import io.circe.syntax._

import java.io.File
import scala.util.{Try, Success, Failure}
import scala.concurrent.{ Await, Future }
import scala.concurrent.duration._

class SplitCallBack(components: Seq[Component])(override implicit val context: inox.Context)
  extends CallBack with CheckFilter with StainlessReports { self =>

  protected final override val trees = extraction.xlang.trees
  protected val pipeline: extraction.StainlessPipeline = extraction.pipeline

  import context.reporter

  private[this] val runs = components.map(_.run(pipeline))

  private implicit val debugSection = DebugSectionFrontend

  /******************* Public Interface: Override CallBack ***************************************/

  final override def beginExtractions(): Unit = {
    assert(tasks.isEmpty)
  }

  final override def apply(
    file: String,
    unit: xt.UnitDef,
    classes: Seq[xt.ClassDef],
    functions: Seq[xt.FunDef],
    typeDefs: Seq[xt.TypeDef]
  ): Unit = {
    reporter.debug(s"Got a unit for $file: ${unit.id} with:")
    reporter.debug(s"\tfunctions -> [${functions.map { _.id }.sorted mkString ", "}]")
    reporter.debug(s"\tclasses   -> [${classes.map { _.id }.sorted mkString ", "}]")
    reporter.debug(s"\ttype defs -> [${typeDefs.map { _.id }.sorted mkString ", "}]")

    this.synchronized {
      recentIdentifiers ++= (classes map (_.id)) ++ (functions map (_.id)) ++ (typeDefs map (_.id))
      toProcess ++= functions map (_.id)

      symbols = symbols.withClasses(classes).withFunctions(functions).withTypeDefs(typeDefs)
    }
  }

  final override def failed(): Unit = ()

  final override def endExtractions(): Unit = {
    symbols = LibraryFilter.removeLibraryFlag(symbols)

    processSymbols(symbols)

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


  /******************* Internal State *************************************************************/

  private val tasks = ListBuffer[Future[Report]]()
  private var report: Report = _

  /** Set of classes/functions seen during the last callback cycle. */
  private val recentIdentifiers = MutableSet[Identifier]()

  /** Set of functions that still need to be processed. */
  private val toProcess = MutableSet[Identifier]()

  /** Current set of symbols */
  private var symbols = xt.NoSymbols

  private val serializer = utils.Serializer(xt)
  import serializer._

  private val canonization = utils.XlangCanonization(xt)

  private val cache = new ConcurrentCache[Identifier, SerializationResult]

  /******************* Internal Helpers ***********************************************************/

  private def processSymbols(syms: xt.Symbols): Unit = {
    val ignoreFlags = Set("library", "synthetic")
    def shouldProcess(id: Identifier): Boolean = {
      !syms.getFunction(id).flags.exists(f => ignoreFlags contains f.name) &&
      this.synchronized {
        val res = toProcess(id)
        toProcess -= id
        res
      }
    }

    for (id <- syms.functions.keys if shouldProcess(id)) {
      processFunction(id, syms)
    }
  }

  private def processFunction(id: Identifier, syms: xt.Symbols): Unit = {
    val fun = syms.functions(id)
    val deps = syms.dependencies(id)
    val clsDeps = syms.classes.values.filter(cd => deps(cd.id)).toSeq
    val funDeps = syms.functions.values.filter(fd => deps(fd.id)).toSeq
    val typeDeps = syms.typeDefs.values.filter(td => deps(td.id)).toSeq
    val preSyms = xt.NoSymbols.withClasses(clsDeps).withFunctions(fun +: funDeps).withTypeDefs(typeDeps)
    val funSyms = Recovery.recover(preSyms)

    val cf = serialize(Right(fun))(funSyms)

    if (!isInCache(id, cf)) {
      processFunctionSymbols(id, funSyms)
      cache.update(id, cf)
    }
  }

  private def processFunctionSymbols(id: Identifier, syms: xt.Symbols): Unit = {
    val errors = TreeSanitizer(xt).enforce(symbols)
    if (!errors.isEmpty) {
      reportErrorFooter(symbols)
    }

    try {
      syms.ensureWellFormed
    } catch {
      case e: syms.TypeErrorException =>
        reportError(e.pos, e.getMessage, syms)
      case e @ xt.NotWellFormedException(defn, _) =>
        reportError(defn.getPos, e.getMessage, syms)
    }

    reporter.debug(s"Solving program with ${syms.functions.size} functions & ${syms.classes.size} classes")

    // Dispatch a task to the executor service instead of blocking this thread.
    val componentReports: Seq[Future[RunReport]] = {
      runs map { run =>
        Try(run(id, syms)) match {
          case Success(future) =>
            val runReport = future map { a =>
              RunReport(run)(a.toReport): RunReport
            }
            runReport

          case Failure(err) =>
            val msg = s"Run has failed with error: $err\n\n" +
                      err.getStackTrace.map(_.toString).mkString("\n")

            reporter.fatalError(msg)
        }
      }
    }

    val futureReport = Future.sequence(componentReports).map(Report)
    this.synchronized { tasks += futureReport }
  }

  private def isInCache(id: Identifier, cf: SerializationResult): Boolean = {
    cache.contains(id) && cache(id) == cf
  }

  private def serialize(node: Either[xt.ClassDef, xt.FunDef])(implicit syms: xt.Symbols): SerializationResult = {
    def getId(node: Either[xt.ClassDef, xt.FunDef]) = node match {
      case Left(cd) => cd.id
      case Right(fd) => fd.id
    }

    val id = getId(node)

    serializer.serialize(canonization(syms, id))
  }

  private def reportError(pos: inox.utils.Position, msg: String, syms: xt.Symbols): Unit = {
    reporter.error(pos, msg)
    reportErrorFooter(syms)
  }

  private def reportErrorFooter(syms: xt.Symbols): Unit = {
    reporter.error(s"The extracted sub-program is not well formed.")
    reporter.error(s"Symbols are:")
    reporter.error(s"functions -> [${syms.functions.keySet.toSeq.sorted mkString ", "}]")
    reporter.error(s"classes   -> [\n  ${syms.classes.values mkString "\n  "}\n]")
    reporter.error(s"typedefs  -> [\n  ${syms.typeDefs.values mkString "\n  "}\n]")
    reporter.fatalError(s"Aborting from SplitCallBack")
  }
}
