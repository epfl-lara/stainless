/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package frontend

import stainless.extraction.xlang.{trees => xt, TreeSanitizer}
import stainless.utils.LibraryFilter

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

  def beginExtractions(): Unit = {}

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
    val allSymbols = xt.NoSymbols
      .withClasses(currentClasses)
      .withFunctions(currentFunctions)
      .withTypeDefs(currentTypeDefs)

    val initialSymbols = LibraryFilter.removeLibraryFlag(allSymbols)

    def notUserFlag(f: xt.Flag) = f.name == "library" || f == xt.Synthetic

    val userIds =
      initialSymbols.classes.values.filterNot(cd => cd.flags.exists(notUserFlag)).map(_.id) ++
      initialSymbols.functions.values.filterNot(fd => fd.flags.exists(notUserFlag)).map(_.id) ++
      initialSymbols.typeDefs.values.filterNot(td => td.flags.exists(notUserFlag)).map(_.id)

    val userDependencies = (userIds.flatMap(initialSymbols.dependencies) ++ userIds).toSeq
    val keepGroups = context.options.findOptionOrDefault(optKeep)

    def hasKeepFlag(flags: Seq[xt.Flag]) =
      keepGroups.exists(g => flags.contains(xt.Annotation("keep", Seq(xt.StringLiteral(g)))))

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
        reportError(e.pos, e.getMessage, symbols)
      case e @ xt.NotWellFormedException(defn, _) =>
        reportError(defn.getPos, e.getMessage, symbols)
    }

    val reports = runs map { run =>
      val ids = symbols.functions.keys.toSeq
      val analysis = Try(Await.result(run(ids, symbols, filterSymbols = true), Duration.Inf))

      analysis match {
        case Success(analysis) =>
          RunReport(run)(analysis.toReport)

        case Failure(err) =>
          val msg = s"Run has failed with error: $err\n\n" + err.getStackTrace.map(_.toString).mkString("\n")
          reporter.fatalError(msg)
      }
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
    reporter.error(s"The extracted program is not well formed.")
    reporter.error(s"Symbols are:")
    reporter.error(s"functions -> [${syms.functions.keySet.toSeq.sorted mkString ", "}]")
    reporter.error(s"classes   -> [\n  ${syms.classes.values mkString "\n  "}\n]")
    reporter.error(s"typedefs  -> [\n  ${syms.typeDefs.values mkString "\n  "}\n]")
    reporter.fatalError(s"Aborting from BatchedCallBack")
  }
}
