/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package frontend

import stainless.extraction.xlang.{trees => xt, TreeSanitizer}
import stainless.utils.LibraryFilter._

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

    val symbolsRmFlag = removeLibraryFlag(allSymbols)

    def notUserFlag(f: xt.Flag) = f.name == "library" || f == xt.Synthetic

    val userIds =
      symbolsRmFlag.classes.values.filterNot(cd => cd.flags.exists(notUserFlag)).map(_.id) ++
      symbolsRmFlag.functions.values.filterNot(fd => fd.flags.exists(notUserFlag)).map(_.id) ++
      symbolsRmFlag.typeDefs.values.filterNot(td => td.flags.exists(notUserFlag)).map(_.id)

    val userDependencies = (userIds.flatMap(id => symbolsRmFlag.dependencies(id)) ++ userIds).toSeq
    val keepGroups = context.options.findOptionOrDefault(optKeep)

    def hasKeepFlag(flags: Seq[xt.Flag]) =
      keepGroups.exists(g => flags.contains(xt.Annotation("keep", Seq(xt.StringLiteral(g)))))

    val preSymbols =
      xt.NoSymbols.withClasses(symbolsRmFlag.classes.values.filter(cd => hasKeepFlag(cd.flags) || userDependencies.contains(cd.id)).toSeq)
                  .withFunctions(symbolsRmFlag.functions.values.filter(fd => hasKeepFlag(fd.flags) || userDependencies.contains(fd.id)).toSeq)
                  .withTypeDefs(symbolsRmFlag.typeDefs.values.filter(td => hasKeepFlag(td.flags) || userDependencies.contains(td.id)).toSeq)

    val symbols = Recovery.recover(preSymbols)

    try {
      TreeSanitizer(xt).check(symbols)
    } catch {
      case e: extraction.MalformedStainlessCode =>
        reportError(e.tree.getPos, e.getMessage, symbols)
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
    reporter.error(s"The extracted program is not well formed.")
    reporter.error(s"Symbols are:")
    reporter.error(s"functions -> [${syms.functions.keySet.toSeq.sorted mkString ", "}]")
    reporter.error(s"classes   -> [\n  ${syms.classes.values mkString "\n  "}\n]")
    reporter.error(s"typedefs  -> [\n  ${syms.typeDefs.values mkString "\n  "}\n]")
    reporter.fatalError(s"Aborting from BatchedCallBack")
  }
}
