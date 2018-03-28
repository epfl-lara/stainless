/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

import utils.JsonUtils

import scala.collection.parallel.ForkJoinTasks
import scala.concurrent.{ ExecutionContext, Future, Await }
import scala.concurrent.duration._
import scala.util.{ Failure, Success }

import java.io.File
import java.util.concurrent.{ Executors, ExecutorService, ForkJoinPool }

import io.circe.Json

object MainHelpers {

  /** See [[frontend.allComponents]]. */
  val components: Seq[Component] = frontend.allComponents

  private lazy val nParallel: Option[Int] =
    Option(System.getProperty("parallel"))
      .flatMap(p => scala.util.Try(p.toInt).toOption)

  private lazy val useParallelism: Boolean =
    (nParallel.isEmpty || nParallel.exists(_ > 1)) &&
    !System.getProperty("os.name").toLowerCase().contains("mac")

  private lazy val currentThreadExecutionContext: ExecutionContext =
    ExecutionContext.fromExecutor(new java.util.concurrent.Executor {
      def execute(runnable: Runnable) { runnable.run() }
    })

  private lazy val multiThreadedExecutor: java.util.concurrent.ExecutorService =
    nParallel.map(Executors.newFixedThreadPool(_)).getOrElse(ForkJoinTasks.defaultForkJoinPool)
  private lazy val multiThreadedExecutionContext: ExecutionContext =
    ExecutionContext.fromExecutor(multiThreadedExecutor)

  implicit def executionContext(implicit ctx: inox.Context): ExecutionContext =
    if (useParallelism && ctx.reporter.debugSections.isEmpty) multiThreadedExecutionContext
    else currentThreadExecutionContext

  def doParallel[A](task: => A)(implicit ctx: inox.Context): Future[A] =
    if (useParallelism && ctx.reporter.debugSections.isEmpty) {
      Future { task }(multiThreadedExecutionContext)
    } else {
      Future.successful(task)
    }

  def parallel[A](tasks: Seq[() => A])(implicit ctx: inox.Context): Seq[A] =
    if (useParallelism && ctx.reporter.debugSections.isEmpty) {
      val futureTasks = tasks.map(task => Future { task() }(multiThreadedExecutionContext))
      Await.result(Future.sequence(futureTasks), Duration.Inf)
    } else {
      tasks.map(_())
    }

  def shutdown(): Unit = if (useParallelism) multiThreadedExecutor.shutdown()
}

trait MainHelpers extends inox.MainHelpers {

  case object Pipelines extends Category
  case object Verification extends Category
  case object Termination extends Category

  override protected def getOptions = super.getOptions - inox.solvers.optAssumeChecked ++ Map(
    optFunctions -> Description(General, "Only consider functions s1,s2,..."),
    evaluators.optCodeGen -> Description(Evaluators, "Use code generating evaluator"),
    codegen.optInstrumentFields -> Description(Evaluators, "Instrument ADT field access during code generation"),
    codegen.optSmallArrays -> Description(Evaluators, "Assume all arrays fit into memory during code generation"),
    verification.optFailEarly -> Description(Verification, "Halt verification as soon as a check fails (invalid or unknown)"),
    verification.optFailInvalid -> Description(Verification, "Halt verification as soon as a check is invalid"),
    verification.optVCCache -> Description(Verification, "Enable caching of verification conditions"),
    verification.optStrictArithmetic -> Description(Verification, "Check arithmetic operations for unintended behaviour and overflows"),
    inox.optTimeout -> Description(General, "Set a timeout n (in sec) such that\n" +
      "  - verification: each proof attempt takes at most n seconds\n" +
      "  - termination: each solver call takes at most n / 100 seconds"),
    termination.optIgnorePosts -> Description(Termination, "Ignore existing postconditions during strengthening"),
    optJson -> Description(General, "Output verification and termination reports to a JSON file"),
    optWatch -> Description(General, "Re-run stainless upon file changes"),
    optCompact -> Description(General, "Print only invalid elements of summaries"),
    frontend.optPersistentCache -> Description(General, "Enable caching of program extraction & analysis"),
    utils.Caches.optCacheDir -> Description(General, "Specify the directory in which cache files should be stored"),
    partialeval.optPartialEvalVC -> Description(Evaluators, "Partially evaluate verification conditions")
  ) ++ MainHelpers.components.map { component =>
    val option = inox.FlagOptionDef(component.name, default = false)
    option -> Description(Pipelines, component.description)
  }

  override protected def getCategories: Seq[Category] = Pipelines +: super.getCategories.filterNot(_ == Pipelines)

  override protected def getDebugSections: Set[inox.DebugSection] = super.getDebugSections ++ Set(
    evaluators.DebugSectionEvaluator,
    verification.DebugSectionVerification,
    verification.DebugSectionCacheHit,
    verification.DebugSectionCacheMiss,
    termination.DebugSectionTermination,
    DebugSectionExtraction,
    frontend.DebugSectionFrontend,
    partialeval.DebugSectionPartialEval,
    utils.DebugSectionRegistry
  )

  override protected def displayVersion(reporter: inox.Reporter): Unit = {
    reporter.title("Stainless verification tool (https://github.com/epfl-lara/stainless)")
  }

  override protected def getName: String = "stainless"

  override protected def displayUsage(reporter: inox.Reporter) = {
    reporter.info("Usage: " +
      Console.BOLD + getName + Console.RESET +
      " [" + Console.UNDERLINED + "OPTION" + Console.RESET + "]... " +
      Console.UNDERLINED + "FILE(S)" + Console.RESET + "..."
    )
  }

  /* NOTE: Should be implemented by a generated Main class in each compiler-specific project: */
  val factory: frontend.FrontendFactory

  final lazy val libraryFiles = factory.libraryFiles

  // TODO add (optional) customisation points for CallBacks to access intermediate reports(?)

  def main(args: Array[String]): Unit = try {
    val ctx = setup(args)
    import ctx.{ reporter, timers }

    if (!MainHelpers.useParallelism) {
      reporter.warning(s"Parallelism is disabled.")
    }

    val compilerArgs = args.toList filterNot { _.startsWith("--") }
    def newCompiler() = frontend.build(ctx, compilerArgs, factory)
    var compiler = newCompiler()

    // For each cycle, passively wait until the compiler has finished
    // & print summary of reports for each component
    def baseRunCycle(): Unit = timers.cycle.run {
      compiler.run()
      compiler.join()

      compiler.getReports foreach { _.emit(ctx) }
    }

    def watchRunCycle() = try {
      baseRunCycle()
    } catch {
      case e: Throwable =>
        reporter.debug(e)(frontend.DebugSectionFrontend)
        reporter.error(e.getMessage)
        compiler = newCompiler()
    }

    def regularRunCycle() = try {
      baseRunCycle()
    } catch {
      case e: inox.FatalError => throw e
      case e: Throwable => reporter.internalError(e)
    }

    val watchMode = isWatchModeOn(ctx)
    if (watchMode) {
      val files: Set[File] = compiler.sources.toSet map {
        file: String => new File(file).getAbsoluteFile
      }
      val watcher = new utils.FileWatcher(ctx, files, action = watchRunCycle)

      watchRunCycle() // first run
      watcher.run()   // subsequent runs on changes
    } else {
      regularRunCycle()
    }

    // Export final results to JSON if asked to.
    ctx.options.findOption(optJson) foreach { file =>
      val output = if (file.isEmpty) optJson.default else file
      reporter.info(s"Printing JSON summary to $output")
      exportJson(compiler.getReports, output)
    }

    reporter.whenDebug(inox.utils.DebugSectionTimers) { debug =>
      timers.outputTable(debug)
    }

    // Shutdown the pool for a clean exit.
    reporter.info("Shutting down executor service.")
    MainHelpers.shutdown()

    val success = compiler.getReports.nonEmpty && (compiler.getReports forall { _.isSuccess })
    System.exit(if (success) 0 else 1)
  } catch {
    case _: inox.FatalError => System.exit(2)
  }

  /** Exports the reports to the given file in JSON format. */
  private def exportJson(reports: Seq[AbstractReport[_]], file: String): Unit = {
    val json = Json.fromFields(reports map { r => (r.name -> r.emitJson) })
    JsonUtils.writeFile(new File(file), json)
  }

}

