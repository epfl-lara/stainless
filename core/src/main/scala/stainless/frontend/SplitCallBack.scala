/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontend

import stainless.utils.LibraryFilter
import extraction.xlang.{TreeSanitizer, trees as xt}
import extraction.utils.ConcurrentCache
import extraction.utils.DebugSymbols
import utils.{CheckFilter, JsonUtils}

import scala.collection.mutable.{ListBuffer, Set as MutableSet}
import io.circe.*
import io.circe.syntax.*
import stainless.extraction.ExtractionFailed

import java.io.File
import scala.util.{Failure, Success, Try}
import scala.concurrent.{Await, Future}
import scala.concurrent.duration.*


class SplitCallBack(components: Seq[Component])(using override val context: inox.Context)
  extends CallBack with CheckFilter with StainlessReports { self =>

  protected final override val trees = extraction.xlang.trees

  private val preprocessing = new DebugSymbols {
    val name = "Preprocessing"
    val context = self.context
    val s: xt.type = xt
    val t: xt.type = xt
  }

  protected val pipeline: extraction.StainlessPipeline = extraction.pipeline

  import context.reporter

  private val runs = components.map(_.run(pipeline))

  private given givenDebugSection: DebugSectionFrontend.type = DebugSectionFrontend

  private case object PreprocessingTag

  /******************* Public Interface: Override CallBack ***************************************/

  final override def beginExtractions(): Unit = {
    assert(tasks.isEmpty)
    recentIdentifiers.clear()
    toProcess.clear()
    symbols = xt.NoSymbols
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

  final override def endExtractions(): Unit = {
    if (reporter.errorCount != 0) {
      reporter.reset()
      throw ExtractionFailed()
    }

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
  private var report: Report = scala.compiletime.uninitialized

  /** Set of classes/functions seen during the last callback cycle. */
  private val recentIdentifiers = MutableSet[Identifier]()

  /** Set of functions that still need to be processed. */
  private val toProcess = MutableSet[Identifier]()

  /** Current set of symbols */
  private var symbols = xt.NoSymbols

  private val serializer = utils.Serializer(xt)
  import serializer._

  private val canonization = utils.XlangCanonization(xt)

  private val cache = new ConcurrentCache[SerializationResult, Future[Report]]

  /******************* Internal Helpers ***********************************************************/

  private def processSymbols(syms: xt.Symbols): Unit = {
    val ignoreFlags = Set("library", "synthetic")
    def shouldProcess(id: Identifier): Set[Identifier] = {
      if (syms.getFunction(id).flags.exists(f => ignoreFlags contains f.name))
        Set()
      else {
        val mutuallyRecursiveDeps =
          syms.dependencies(id)
            .filter(syms.lookupFunction(_).nonEmpty)
            .filter(id2 => syms.dependencies(id2).contains(id))
        this.synchronized {
          val res = (mutuallyRecursiveDeps + id).filter(toProcess)
          toProcess -= id
          toProcess --= mutuallyRecursiveDeps
          res
        }
      }
    }
    reportProgress("Preprocessing the symbols...")
    processFunctions(syms.functions.keys.flatMap(shouldProcess).toSet, syms)
  }

  private def processFunctions(ids: Set[Identifier], syms: xt.Symbols): Unit = {
    val funs = ids.map(syms.functions)
    val deps = ids.flatMap(syms.dependencies)
    val clsDeps = syms.classes.values.filter(cd => deps(cd.id)).toSeq
    val funDeps = syms.functions.values.filter(fd => deps(fd.id)).toSeq
    val typeDeps = syms.typeDefs.values.filter(td => deps(td.id)).toSeq
    val preSyms = xt.NoSymbols.withClasses(clsDeps).withFunctions(funDeps ++ funs).withTypeDefs(typeDeps)
    val funSyms = preprocessing.debugWithoutSummary(Preprocessing().transform)(preSyms)._1

    val cf = serialize(funs)(using funSyms)

    val futureReport = cache.getOrElseUpdate(cf, processFunctionsSymbols(ids, funSyms))
    this.synchronized { tasks += futureReport }
  }

  private def processFunctionsSymbols(ids: Set[Identifier], syms: xt.Symbols): Future[Report] = {
    val errors = TreeSanitizer(xt).enforce(syms)
    if (!errors.isEmpty) {
      reportErrorFooter(syms)
    }

    try {
      syms.ensureWellFormed
    } catch {
      case e: syms.TypeErrorException =>
        reporter.debug(e)
        reportError(e.pos, e.getMessage, syms)
      case e @ xt.NotWellFormedException(defn, _) =>
        reporter.debug(e)
        reportError(defn.getPos, e.getMessage, syms)
    }

    reportProgress("Preprocessing finished")
    reporter.debug(s"Solving program with ${syms.functions.size} functions & ${syms.classes.size} classes")

    // Dispatch a task to the executor service instead of blocking this thread.
    val componentReports: Seq[Future[RunReport]] = {
      runs map { run =>
        run(ids.toSeq, syms) map { a =>
          RunReport(run)(a.toReport): RunReport
        }
      }
    }

    Future.sequence(componentReports).map(Report.apply)
  }

  private def serialize(fds: Set[xt.FunDef])(using syms: xt.Symbols): SerializationResult = {
    serializer.serialize(canonization(syms, fds.toSeq.map(_.id).sorted))
  }

  private def reportError(pos: inox.utils.Position, msg: String, syms: xt.Symbols): Unit = {
    reporter.error(pos, msg)
    reportErrorFooter(syms)
  }

  private def reportErrorFooter(syms: xt.Symbols): Unit = {
    reporter.debug(s"The extracted sub-program is not well formed.")
    reporter.debug(s"Symbols are:")
    reporter.debug(s"functions -> [${syms.functions.keySet.toSeq.sorted mkString ", "}]")
    reporter.debug(s"classes   -> [\n  ${syms.classes.values mkString "\n  "}\n]")
    reporter.debug(s"typedefs  -> [\n  ${syms.typeDefs.values mkString "\n  "}\n]")
    reporter.fatalError(s"Well-formedness check failed after extraction")
  }

  private def reportProgress(msg: String) =
    context.reporter.emit(context.reporter.ProgressMessage(context.reporter.INFO, PreprocessingTag, msg))
}
