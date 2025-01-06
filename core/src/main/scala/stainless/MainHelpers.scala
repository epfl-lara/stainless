/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import utils.JsonUtils
import java.io.File

import io.circe.Json

object MainHelpers {

  /** See [[frontend.allComponents]]. */
  val components: Seq[Component] = frontend.allComponents
}

trait MainHelpers extends inox.MainHelpers { self =>

  object optVersion extends inox.FlagOptionDef("version", false)

  case object Pipelines extends Category
  case object Verification extends Category
  case object Termination extends Category
  case object TestsGeneration extends Category {
    override def toString: String = "Tests Generation"
  }
  case object EquivChk extends Category {
    override def toString: String = "Equivalence checking"
  }

  override protected def getOptions: Map[inox.OptionDef[?], Description] = super.getOptions - inox.solvers.optAssumeChecked ++ Map(
    optVersion -> Description(General, "Display the version number"),
    optConfigFile -> Description(General, "Path to configuration file, set to false to disable (default: stainless.conf or .stainless.conf)"),
    optFunctions -> Description(General, "Only consider functions f1,f2,..."),
    extraction.utils.optDebugObjects -> Description(General, "Only print debug output for functions/adts named o1,o2,..."),
    extraction.utils.optDebugPhases -> Description(General, {
      // f interpolator does not process escape sequence, we workaround that with the following trick.
      // See https://github.com/lampepfl/dotty/issues/11750
      val nl = '\n'
      "Only print debug output for phases p1,p2,...\nAvailable: " +
      extraction.phases.map { case (name, desc) => f"$nl  $name%-26s : $desc" }.mkString("")
    }),
    extraction.imperative.optFullImperative -> Description(Verification, "Use the full imperative phase. That might be unstable because it is still under development."),
    extraction.imperative.optCheckHeapContracts -> Description(Verification, "Check that heap reads and modifies clauses are valid"),
    evaluators.optCodeGen -> Description(Evaluators, "Use code generating evaluator"),
    codegen.optInstrumentFields -> Description(Evaluators, "Instrument ADT field access during code generation"),
    codegen.optSmallArrays -> Description(Evaluators, "Assume all arrays fit into memory during code generation"),
    verification.optSilent -> Description(Verification, "Do not print any message when a verification condition fails due to invalidity or timeout"),
    verification.optFailEarly -> Description(Verification, "Halt verification as soon as a check fails (invalid or unknown)"),
    verification.optFailInvalid -> Description(Verification, "Halt verification as soon as a check is invalid"),
    verification.optVCCache -> Description(Verification, "Enable caching of verification conditions"),
    verification.optCoq -> Description(Verification, "Transform the program into a Coq program, and let Coq generate subgoals automatically"),
    verification.optAdmitAll -> Description(Verification, "Admit all obligations when translated into a coq program"),
    verification.optStrictArithmetic -> Description(Verification, "Check arithmetic operations for unintended behavior and overflows"),
    verification.optAdmitVCs -> Description(Verification, "Admit all verification conditions"),
    verification.optSimplifier -> Description(Verification, "Select which simplifier to use for VC simplification\n" +
      "Available:\n" +
      "  vanilla:             : Standard simplifier\n" +
      "  ol (experimental)    : Leverages ortholattice algebra for simplifying boolean expressions\n" +
      "  ocbsl (experimental) : Leverages orthocomplemented bisemilattices boolean algebra for simplifying boolean expressions.\n" +
      "                         Though the name sounds cooler than OL, it is less complete.\n" +
      "  bland (experimental) : Common simplification logic to OL and OCBSL, but without any boolean algebra flavor"),
    termination.optCheckMeasures -> Description(Termination, "Check that measures are valid (both inferred and user-defined)"),
    termination.optInferMeasures -> Description(Termination, "Automatically infer measures for recursive functions"),
    inox.optTimeout -> Description(General, "Set a timeout n (in sec) such that\n" +
      "  - verification: each proof attempt takes at most n seconds\n" +
      "  - termination: each solver call takes at most n / 100 seconds"),
    optJson -> Description(General, "Output verification and termination reports to a JSON file"),
    genc.optOutputFile -> Description(General, "File name for GenC output"),
    genc.optIncludes -> Description(General, "Add includes in GenC output"),
    optWatch -> Description(General, "Re-run stainless upon file changes"),
    optCompact -> Description(General, "Print only invalid elements of summaries"),
    optExtendedSummary -> Description(General, "Print an extended summary of all Stainless phases"),
    frontend.optBatchedProgram -> Description(General, "Process the whole program together, skip dependency analysis"),
    frontend.optKeep -> Description(General, "Keep library objects marked by @keepFor(g) for some g in g1,g2,... (implies --batched)"),
    frontend.optExtraDeps -> Description(General, "Fetch the specified extra source dependencies and add their source files to the session"),
    frontend.optExtraResolvers -> Description(General, "Extra resolvers to use to fetch extra source dependencies"),
    frontend.optClasspath -> Description(General, "Add the specified directory to the classpath"),
    utils.Caches.optCacheDir -> Description(General, "Specify the directory in which cache files should be stored"),
    utils.Caches.optBinaryCache -> Description(General, "Set Binary mode for the cache instead of Hash mode, i.e., the cache will contain the entire VC and program in serialized format. This is less space efficient."),
    testgen.optOutputFile -> Description(TestsGeneration, "Specify the output file"),
    testgen.optGenCIncludes -> Description(TestsGeneration, "(GenC variant only) Specify header includes"),
    equivchk.optCompareFuns -> Description(EquivChk, "Only consider functions f1,f2,... for equivalence checking"),
    equivchk.optModels -> Description(EquivChk, "Consider functions f1, f2, ... as model functions for equivalence checking"),
    equivchk.optNorm -> Description(EquivChk, "Use function f as normalization function for equivalence checking"),
    equivchk.optEquivalenceOutput -> Description(EquivChk, "JSON output file for equivalence checking"),
    equivchk.optN -> Description(EquivChk, "Consider the top N models"),
    equivchk.optInitScore -> Description(EquivChk, "Initial score for models"),
    equivchk.optInitWeights -> Description(EquivChk, "Initial weights for models, overriding the initial score"),
    equivchk.optMaxPerm -> Description(EquivChk, "Maximum number of permutations to be tested when matching auxiliary functions"),
    equivchk.optMaxCtex -> Description(EquivChk, "Maximum number of counter-examples to collect"),
    equivchk.optMeasureTransfer -> Description(EquivChk, "Enable measure transfer for candidate functions"),
    optSatPrecond -> Description(General, "Generate VCs to check that preconditions are SAT"),
  ) ++ MainHelpers.components.map { component =>
    val option = inox.FlagOptionDef(component.name, default = false)
    option -> Description(Pipelines, component.description)
  }

  override protected def getCategories: Seq[Category] = Pipelines +: super.getCategories.filterNot(_ == Pipelines)

  override protected def getDebugSections: Set[inox.DebugSection] = super.getDebugSections ++ Set(
    evaluators.DebugSectionEvaluator,
    verification.DebugSectionVerification,
    verification.DebugSectionFullVC,
    verification.DebugSectionCacheHit,
    verification.DebugSectionCacheMiss,
    verification.DebugSectionCoq,
    verification.DebugSectionPartialEval,
    verification.DebugSectionTypeChecker,
    verification.DebugSectionTypeCheckerVCs,
    verification.DebugSectionDerivation,
    termination.DebugSectionTermination,
    termination.DebugSectionMeasureInference,
    extraction.inlining.DebugSectionFunctionSpecialization,
    extraction.utils.DebugSectionTrees,
    extraction.utils.DebugSectionSizes,
    extraction.utils.DebugSectionPositions,
    frontend.DebugSectionCallGraph,
    frontend.DebugSectionExtraction,
    frontend.DebugSectionFrontend,
    frontend.DebugSectionStack,
    frontend.DebugSectionRecovery,
    frontend.DebugSectionExtraDeps,
    genc.DebugSectionGenC,
    equivchk.DebugSectionEquivChk
  )

  override protected def displayVersion(reporter: inox.Reporter): Unit = {
    reporter.title("Stainless verification tool (https://github.com/epfl-lara/stainless)")
    reporter.info(s"  Version: ${BuildInfo.version}")
    reporter.info(s"  Built at: ${BuildInfo.builtAtString}")
    reporter.info(s"  Stainless Scala version: ${BuildInfo.scalaVersion}")
    super.displayVersion(reporter)
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

  override
  protected def newReporter(debugSections: Set[inox.DebugSection]): inox.Reporter =
    new stainless.DefaultReporter(debugSections)

  def getConfigOptions(options: inox.Options)(using inox.Reporter): Seq[inox.OptionValue[?]] = {
    Configuration.get(options, self.options.keys.toSeq)
  }

  def getConfigContext(options: inox.Options)(using inox.Reporter): inox.Context = {
    val ctx = super.processOptions(Seq.empty, getConfigOptions(options))

    if (ctx.options.findOptionOrDefault(inox.optNoColors)) {
      val reporter = new stainless.PlainTextReporter(ctx.reporter.debugSections)
      Context.withReporter(reporter)(ctx)
    } else ctx
  }

  override
  protected def processOptions(files: Seq[File], cmdOptions: Seq[inox.OptionValue[?]])
                              (using inox.Reporter): inox.Context = {
    val configOptions = getConfigOptions(inox.Options(cmdOptions))

    // Override config options with command-line options
    val options = (cmdOptions ++ configOptions)
      .groupBy(_.optionDef.name)
      .view.mapValues(_.head)
      .values
      .toSeq

    val ctx = super.processOptions(files, options)

    if (ctx.options.findOptionOrDefault(inox.optNoColors)) {
      val reporter = new stainless.PlainTextReporter(ctx.reporter.debugSections)
      Context.withReporter(reporter)(ctx)
    } else ctx
  }

  def main(args: Array[String]): Unit = {
    val ctx: inox.Context = try {
      setup(args)
    } catch {
      case e: Throwable =>
        topLevelErrorHandler(e)(using Context.empty)
    }
    import ctx.given
    try {
      if (ctx.options.findOptionOrDefault(optVersion)) {
        displayVersion(ctx.reporter)
        System.exit(0)
      }

      import ctx.{reporter, timers}
      if (!useParallelism) {
        reporter.warning(s"Parallelism is disabled.")
      }

      val compilerArgs = args.toList filterNot { _.startsWith("--") }
      def newCompiler() = frontend.build(ctx, compilerArgs, factory)
      var compiler = newCompiler()

      // For each cycle, passively wait until the compiler has finished
      // & print summary of reports for each component
      def baseRunCycle(): Unit = timers.cycle.run {
        // reset the global VC counters for displaying progress
        verification.VerificationChecker.reset()
        compiler.run()
        compiler.join()

        compiler.getReport foreach { _.emit(ctx) }
      }

      def watchRunCycle() = try {
        baseRunCycle()
      } catch {
        case extraction.ExtractionFailed() =>
          // The errors have already been printed, there is nothing special to do.
        case e @ extraction.MalformedStainlessCode(tree, msg) =>
          reporter.debug(e)(using frontend.DebugSectionStack)
          ctx.reporter.error(tree.getPos, msg)
        case e @ inox.FatalError(msg) =>
          // we don't print the error message in this case because it was already printed before
          // the `FatalError` was thrown
          reporter.debug(e)(using frontend.DebugSectionStack)
        case e: Throwable =>
          reporter.debug(e)(using frontend.DebugSectionStack)
          reporter.error(Option(e.getMessage).getOrElse(""))
      } finally {
        reporter.reset()
        compiler = newCompiler()
      }

      val watchMode = isWatchModeOn
      if (watchMode) {
        val files: Set[File] = compiler.sources.toSet map {
          (file: String) => new File(file).getAbsoluteFile
        }
        val watcher = new utils.FileWatcher(ctx, files, action = () => watchRunCycle())

        watchRunCycle() // first run
        watcher.run()   // subsequent runs on changes
      } else {
        baseRunCycle()
      }

      // Export final results to JSON if asked to.
      ctx.options.findOption(optJson) foreach { file =>
        val output = if (file.isEmpty) optJson.default else file
        reporter.info(s"Printing JSON summary to $output")
        exportJson(compiler.getReport, output)
      }

      val asciiOnly = ctx.options.findOptionOrDefault(inox.optNoColors)
      reporter.whenDebug(inox.utils.DebugSectionTimers) { debug =>
        timers.outputTable(debug, asciiOnly)
      }

      // Shutdown the pool for a clean exit.
      reporter.info("Shutting down executor service.")
      stainless.shutdown()

      val success = compiler.getReport.exists(_.isSuccess)
      System.exit(if (success) 0 else 1)
    } catch {
      case e: Throwable => topLevelErrorHandler(e)
    }
  }

  /** Exports the reports to the given file in JSON format. */
  private def exportJson(report: Option[AbstractReport[?]], file: String): Unit = {
    val json = Json.fromFields(report map { r => (r.name -> r.emitJson) })
    JsonUtils.writeFile(new File(file), json)
  }
}
