/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontend

import stainless.extraction.xlang.{trees => xt, TreeSanitizer}
import stainless.utils.LibraryFilter
import stainless.extraction.trace.Trace

import scala.util.{Try, Success, Failure}
import scala.concurrent.Await
import scala.concurrent.duration._

class BatchedCallBack(components: Seq[Component])(implicit val context: inox.Context) extends CallBack with StainlessReports {
  import context.reporter

  private implicit val debugSection = DebugSectionFrontend

  private var currentClasses = Seq[xt.ClassDef]()
  private var currentFunctions = Seq[xt.FunDef]()
  private var currentTypeDefs = Seq[xt.TypeDef]()

  private var report: AbstractReport[Report] = _

  protected val pipeline: extraction.StainlessPipeline = extraction.pipeline
  private[this] val runs = components.map(_.run(pipeline))

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

  def failed(): Unit = {}

  def endExtractions(): Unit = {
    context.reporter.terminateIfFatal()

    val allSymbols = xt.NoSymbols
      .withClasses(currentClasses)
      .withFunctions(currentFunctions)
      .withTypeDefs(currentTypeDefs)

    val initialSymbols = strictBVCleaner.transform(LibraryFilter.removeLibraryFlag(allSymbols))

    def notUserFlag(f: xt.Flag) = f.name == "library" || f == xt.Synthetic

    val userIds =
      initialSymbols.classes.values.filterNot(cd => cd.flags.exists(notUserFlag)).map(_.id) ++
      initialSymbols.functions.values.filterNot(fd => fd.flags.exists(notUserFlag)).map(_.id) ++
      initialSymbols.typeDefs.values.filterNot(td => td.flags.exists(notUserFlag)).map(_.id)

    val userDependencies = (userIds.flatMap(initialSymbols.dependencies) ++ userIds).toSeq
    val keepGroups = context.options.findOptionOrDefault(optKeep)

    def hasKeepFlag(flags: Seq[xt.Flag]) =
      flags.exists(_.name == "keep") ||
      keepGroups.exists(g => flags.contains(xt.Annotation("keepFor", Seq(xt.StringLiteral(g)))))

    def keepDefinition(defn: xt.Definition): Boolean =
      hasKeepFlag(defn.flags) || userDependencies.contains(defn.id)

    val preSymbols =
      xt.NoSymbols.withClasses(initialSymbols.classes.values.filter(keepDefinition).toSeq)
                  .withFunctions(initialSymbols.functions.values.filter(keepDefinition).toSeq)
                  .withTypeDefs(initialSymbols.typeDefs.values.filter(keepDefinition).toSeq)

    val symbols = Recovery.recover(preSymbols)

    val errors = TreeSanitizer(xt).enforce(symbols)
    if (!errors.isEmpty) {
      reportErrorFooter(symbols)
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

    var rerunPipeline = true

    while (rerunPipeline) {
      val reports = runs map { run =>
        val ids = symbols.functions.keys.toSeq
        val analysis = Await.result(run(ids, symbols, filterSymbols = true), Duration.Inf)
        RunReport(run)(analysis.toReport)
      }

      report = Report(reports)
      rerunPipeline = Trace.nextIteration(report)

      if (rerunPipeline) report.emit(context)
      else Trace.printEverything
    }
    
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
