/* Copyright 2009-2018 EPFL, Lausanne */

package stainless

import utils.JsonUtils

import scala.util.{ Failure, Success }

import java.io.File

import io.circe.Json

object MainHelpers {

  /** See [[frontend.allComponents]]. */
  val components: Seq[Component] = frontend.allComponents
}

trait MainHelpers extends inox.MainHelpers {

  case object Pipelines extends Category
  case object Verification extends Category
  case object Termination extends Category

  override protected def getOptions = super.getOptions - inox.solvers.optAssumeChecked ++ Map(
    optFunctions -> Description(General, "Only consider functions f1,f2,..."),
    optDebugObjects -> Description(General, "Only print debug output for functions/adts named o1,o2,..."),
    optDebugPhases -> Description(General, "Only print debug output for phases whose name contain p1 or p2 or ..."),
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
    utils.Caches.optCacheDir -> Description(General, "Specify the directory in which cache files should be stored")
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
    verification.DebugSectionPartialEval,
    termination.DebugSectionTermination,
    DebugSectionExtraction,
    extraction.DebugSectionTrees,
    extraction.utils.DebugSectionPositions,
    frontend.DebugSectionFrontend,
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

    if (!useParallelism) {
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

      compiler.getReport foreach { _.emit(ctx) }
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
      exportJson(compiler.getReport, output)
    }

    reporter.whenDebug(inox.utils.DebugSectionTimers) { debug =>
      timers.outputTable(debug)
    }

    // Shutdown the pool for a clean exit.
    reporter.info("Shutting down executor service.")
    stainless.shutdown()

    val success = compiler.getReport.exists(_.isSuccess)
    System.exit(if (success) 0 else 1)
  } catch {
    case _: inox.FatalError => System.exit(2)
  }

  /** Exports the reports to the given file in JSON format. */
  private def exportJson(report: Option[AbstractReport[_]], file: String): Unit = {
    val json = Json.fromFields(report map { r => (r.name -> r.emitJson) })
    JsonUtils.writeFile(new File(file), json)
  }
}

