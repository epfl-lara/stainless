/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package frontend

import stainless.extraction.xlang.{trees => xt, TreeSanitizer}

import scala.util.{Try, Success, Failure}
import scala.concurrent.Await
import scala.concurrent.duration._

class BatchedCallBack(components: Seq[Component])(implicit val context: inox.Context) extends CallBack with StainlessReports {
  import context.reporter

  private var currentClasses = Seq[xt.ClassDef]()
  private var currentFunctions = Seq[xt.FunDef]()

  private var report: AbstractReport[Report] = _

  protected val pipeline: extraction.StainlessPipeline = extraction.pipeline
  private[this] val runs = components.map(_.run(pipeline))

  def beginExtractions(): Unit = {}

  def apply(file: String, unit: xt.UnitDef, classes: Seq[xt.ClassDef], functions: Seq[xt.FunDef]): Unit = {
    synchronized {
      currentFunctions ++= functions
      currentClasses ++= classes
    }
  }

  def failed(): Unit = {}

  def endExtractions(): Unit = {
    val allSymbols = xt.NoSymbols.withClasses(currentClasses).withFunctions(currentFunctions)
    def notUserFlag(f: xt.Flag) = f.name == "library" || f == xt.Synthetic
    val userIds =
      currentClasses.filterNot(cd => cd.flags.exists(notUserFlag)).map(_.id) ++
      currentFunctions.filterNot(fd => fd.flags.exists(notUserFlag)).map(_.id)
    val userDependencies = userIds.flatMap(id => allSymbols.dependencies(id) ) ++ userIds
    val keepGroups = context.options.findOptionOrDefault(optKeep)
    def hasKeepFlag(flags: Seq[xt.Flag]) =
      keepGroups.exists(g => flags.contains(xt.Annotation("keep",Seq(g))))

    val symbols =
      xt.NoSymbols.withClasses(currentClasses.filter(cd => hasKeepFlag(cd.flags) || userDependencies.contains(cd.id)))
                  .withFunctions(currentFunctions.filter(fd => hasKeepFlag(fd.flags) || userDependencies.contains(fd.id)))

    try {
      TreeSanitizer(xt).check(symbols)
    } catch {
      case e: extraction.MalformedStainlessCode =>
        reportError(e.tree.getPos, e.getMessage, symbols)
    }

    val reports = runs map { run =>
      val ids = symbols.functions.keys.toSeq
      val analysis = Try(run(ids, symbols, filterSymbols = true))
      analysis match {
        case Success(analysis) =>
          val report = Await.result(analysis, Duration.Inf).toReport
          Some(RunReport(run)(report))

        case Failure(err) =>
          reporter.error(s"Run has failed with error: $err")
          None
      }
    }
    report = Report(reports collect { case Some(r) => r })
  }

  def stop(): Unit = {
    currentClasses = Seq()
    currentFunctions = Seq()
  }

  def join(): Unit = {}

  def getReport = Option(report)

  private def reportError(pos: inox.utils.Position, msg: String, syms: xt.Symbols): Unit = {
    reporter.error(pos, msg)
    reporter.error(s"The extracted sub-program in not well formed.")
    reporter.error(s"Symbols are:")
    reporter.error(s"functions -> [${syms.functions.keySet.toSeq.sorted mkString ", "}]")
    reporter.error(s"classes   -> [\n  ${syms.classes.values mkString "\n  "}\n]")
    reporter.fatalError(s"Aborting from SplitCallBack")
  }
}
