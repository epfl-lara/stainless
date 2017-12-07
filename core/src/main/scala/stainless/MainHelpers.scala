/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import utils.JsonUtils

import scala.collection.parallel.{ ExecutionContextTaskSupport, ForkJoinTasks }
import scala.concurrent.ExecutionContext

import java.io.File
import java.util.concurrent.{ Executors, ExecutorService }

import io.circe.Json

object MainHelpers {

  /** See [[frontend.allComponents]]. */
  val components: Seq[Component] = frontend.allComponents

  val useParallelism = !System.getProperty("os.name").toLowerCase().contains("mac")

  /** Executor used to execute tasks concurrently. */
  // FIXME ideally, we should use the same underlying pool for the frontends' compiler...
  // TODO add an option for the number of thread? (need to be moved in trait MainHelpers then).
  val executor: ExecutorService = {
    // Don't use a different parallel executor or `par` will dead lock.
    if (useParallelism) ForkJoinTasks.defaultForkJoinPool
    else Executors.newSingleThreadExecutor()
  }

  /**
   * Set up a parallel collection if parallelism is enabled.
   *
   * When parallelism is turned on, the returned parallel collection used the
   * [[MainHelpers.executor]] to dispatch & balance tasks.
   */
  def par[A](collection: Seq[A]) = {
    if (useParallelism) {
      val pc = collection.par
      pc.tasksupport = new ExecutionContextTaskSupport(ExecutionContext.fromExecutorService(executor))
      pc
    } else {
      collection
    }
  }
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
    frontend.optPersistentCache -> Description(General, "Enable caching of program extraction & analysis"),
    utils.Caches.optCacheDir -> Description(General, "Specify the directory in which cache files should be stored")
  ) ++ MainHelpers.components.map { component =>
    val option = inox.FlagOptionDef(component.name, default = false)
    option -> Description(Pipelines, component.description)
  }

  override protected def getCategories: Seq[Category] = Pipelines +: super.getCategories.filterNot(_ == Pipelines)

  override protected def getDebugSections: Set[inox.DebugSection] = super.getDebugSections ++ Set(
    verification.DebugSectionVerification,
    verification.DebugSectionCacheHit,
    verification.DebugSectionCacheMiss,
    termination.DebugSectionTermination,
    DebugSectionExtraction,
    frontend.DebugSectionFrontend,
    utils.DebugSectionRegistry
  )

  override protected def displayVersion(reporter: inox.Reporter): Unit = {
    reporter.title("Stainless verification tool (https://github.com/epfl-lara/stainless)")
  }

  override protected def getName: String = "stainless"

  /* NOTE: Should be implemented by a generated Main class in each compiler-specific project: */
  val factory: frontend.FrontendFactory

  final lazy val libraryFiles = factory.libraryFiles

  // TODO add (optional) customisation points for CallBacks to access intermediate reports(?)

  def main(args: Array[String]): Unit = try {
    val ctx = setup(args)

    if (!MainHelpers.useParallelism) {
      ctx.reporter.warning(s"Parallelism is disabled.")
    }

    val compilerArgs = args.toList filterNot { _.startsWith("--") }
    val compiler = frontend.build(ctx, compilerArgs, factory)

    // For each cylce, passively wait until the compiler has finished
    // & print summary of reports for each component
    def runCycle() = try {
      compiler.run()
      compiler.join()

      compiler.getReports foreach { _.emit(ctx) }
    } catch {
      case frontend.UnsupportedCodeException(pos, msg) =>
        ctx.reporter.error(pos, msg)
    }

    // Run the first cycle
    runCycle()

    val watchMode = isWatchModeOn(ctx)
    if (watchMode) {
      val files: Set[File] = compiler.sources.toSet map { file: String => new File(file).getAbsoluteFile }
      val watcher = new utils.FileWatcher(ctx, files, action = runCycle)
      watcher.run()
    }

    // Export final results to JSON if asked to.
    ctx.options.findOption(optJson) foreach { file =>
      val output = if (file.isEmpty) optJson.default else file
      ctx.reporter.info(s"Printing JSON summary to $output")
      exportJson(compiler.getReports, output)
    }

    ctx.reporter.whenDebug(inox.utils.DebugSectionTimers) { debug =>
      ctx.timers.outputTable(debug)
    }

    // Shutdown the pool for a clean exit.
    ctx.reporter.info("Shutting down executor service.")
    MainHelpers.executor.shutdown()

    System.exit(if (compiler.getReports.nonEmpty && (compiler.getReports forall { _.isSuccess })) 0 else 1)
  } catch {
    case _: inox.FatalError => System.exit(2)
  }

  /** Exports the reports to the given file in JSON format. */
  private def exportJson(reports: Seq[AbstractReport[_]], file: String): Unit = {
    val json = Json.fromFields(reports map { r => (r.name -> r.emitJson) })
    JsonUtils.writeFile(new File(file), json)
  }

}

