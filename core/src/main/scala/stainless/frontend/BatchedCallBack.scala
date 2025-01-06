/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontend

import stainless.extraction.ExtractionFailed
import stainless.extraction.xlang.{TreeSanitizer, trees as xt}
import stainless.extraction.utils.DebugSymbols
import stainless.utils.LibraryFilter

import scala.util.{Failure, Success, Try}
import scala.concurrent.Await
import scala.concurrent.duration.*

class BatchedCallBack(components: Seq[Component])(using val context: inox.Context) extends CallBack with StainlessReports { self =>
  import context.reporter

  private given givenDebugSection: DebugSectionFrontend.type = DebugSectionFrontend

  private case object PreprocessingTag

  private var currentClasses = Seq[xt.ClassDef]()
  private var currentFunctions = Seq[xt.FunDef]()
  private var currentTypeDefs = Seq[xt.TypeDef]()

  private var report: AbstractReport[Report] = scala.compiletime.uninitialized

  private val preprocessing = new DebugSymbols {
    val name = "Preprocessing"
    val context = self.context
    val s: xt.type = xt
    val t: xt.type = xt
  }

  private val userFiltering = new DebugSymbols {
    val name = "UserFiltering"
    val context = self.context
    val s: xt.type = xt
    val t: xt.type = xt
  }

  protected val pipeline: extraction.StainlessPipeline = extraction.pipeline
  private val runs = components.map(_.run(pipeline))

  def beginExtractions(): Unit = {
    currentClasses = Seq()
    currentFunctions = Seq()
    currentTypeDefs = Seq()
  }

  override def apply(
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
      currentFunctions ++= functions
      currentClasses ++= classes
      currentTypeDefs ++= typeDefs
    }
  }

  def endExtractions(): Unit = {
    def reportProgress(msg: String) =
      context.reporter.emit(context.reporter.ProgressMessage(context.reporter.INFO, PreprocessingTag, msg))

    if (reporter.errorCount != 0) {
      reporter.reset()
      throw ExtractionFailed()
    }

    reportProgress("Preprocessing the symbols...")
    val allSymbols = xt.NoSymbols
      .withClasses(currentClasses)
      .withFunctions(currentFunctions)
      .withTypeDefs(currentTypeDefs)

    val symbols =
      userFiltering.debugWithoutSummary(UserFiltering().transform)(
        preprocessing.debugWithoutSummary(Preprocessing().transform)(
          allSymbols
        )._1
      )._1

    val errors = TreeSanitizer(xt).enforce(symbols)
    if (!errors.isEmpty) {
      reportErrorFooter(symbols)
    }

    if (context.reporter.isDebugEnabled(using DebugSectionCallGraph)) {
      CallGraphPrinter(symbols)
    }

    try {
      symbols.ensureWellFormed
    } catch {
      case e: symbols.TypeErrorException =>
        reporter.debug(e)
        reportError(e.pos, e.getMessage, symbols)
      case e @ xt.NotWellFormedException(defn, _) =>
        reporter.debug(e)
        reportError(defn.getPos, e.getMessage, symbols)
    }

    reportProgress("Preprocessing finished")

    val reports = runs map { run =>
      val ids = symbols.functions.keys.toSeq
      val analysis = Await.result(run(ids, symbols), Duration.Inf)
      RunReport(run)(analysis.toReport)
    }
    report = Report(reports)
  }

  def stop(): Unit = {
    currentClasses = Seq()
    currentFunctions = Seq()
    currentTypeDefs = Seq()
  }

  def join(): Unit = {}

  def getReport = Option(report)

  private def reportError(pos: inox.utils.Position, msg: String, syms: xt.Symbols): Unit = {
    reporter.error(pos, msg)
    reportErrorFooter(syms)
  }

  private def reportErrorFooter(syms: xt.Symbols): Unit = {
    reporter.debug(s"The extracted program is not well formed.")
    reporter.debug(s"Symbols are:")
    reporter.debug(s"functions -> [${syms.functions.keySet.toSeq.sorted mkString ", "}]")
    reporter.debug(s"classes   -> [\n  ${syms.classes.values mkString "\n  "}\n]")
    reporter.debug(s"typedefs  -> [\n  ${syms.typeDefs.values mkString "\n  "}\n]")
    reporter.fatalError(s"Well-formedness check failed after extraction")
  }
}
