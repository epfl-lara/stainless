/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import java.io.{ File, PrintWriter }
import java.nio.file.{ FileSystems, Path, StandardWatchEventKinds }
import java.util.concurrent.{ Executors, TimeUnit }

import scala.collection.JavaConversions._
import scala.collection.mutable.{ Map => MutableMap }

import org.json4s.JsonAST.JObject
import org.json4s.JsonDSL._
import org.json4s.native.JsonMethods._

object MainHelpers {

  /** See [[frontend.allComponents]]. */
  val components = frontend.allComponents

  /** Executor used to execute tasks concurrently. */
  // FIXME ideally, we should use the same underlying pool for the frontends' compiler...
  // TODO add an option for the number of thread? (need to be moved in trait MainHelpers then).
  // val executor = Executors.newWorkStealingPool(Runtime.getRuntime.availableProcessors - 2)
  val executor = Executors.newWorkStealingPool()
  // val executor = Executors.newSingleThreadExecutor()

}

trait MainHelpers extends inox.MainHelpers {

  case object Pipelines extends Category
  case object Verification extends Category
  case object Termination extends Category

  object optJson extends inox.OptionDef[String] {
    val name = "json"
    val default = "report.json"
    val parser = inox.OptionParsers.stringParser
    val usageRhs = "file"
  }

  object optWatch extends inox.FlagOptionDef("watch", false)

  override protected def getOptions = super.getOptions ++ Map(
    optFunctions -> Description(General, "Only consider functions s1,s2,..."),
    evaluators.optCodeGen -> Description(Evaluators, "Use code generating evaluator"),
    codegen.optInstrumentFields -> Description(Evaluators, "Instrument ADT field access during code generation"),
    codegen.optSmallArrays -> Description(Evaluators, "Assume all arrays fit into memory during code generation"),
    verification.optParallelVCs -> Description(Verification, "Check verification conditions in parallel"),
    verification.optFailEarly -> Description(Verification, "Halt verification as soon as a check fails"),
    verification.VerificationComponent.optStrictArithmetic -> Description(Verification, "Check arithmetic operations for unintended behaviour and overflows"),
    inox.optTimeout -> Description(General, "Set a timeout n (in sec) such that\n" +
      "  - verification: each proof attempt takes at most n seconds\n" +
      "  - termination: each solver call takes at most n / 100 seconds"),
    extraction.inlining.optInlinePosts -> Description(General, "Inline postconditions at call-sites"),
    termination.optIgnorePosts -> Description(Termination, "Ignore existing postconditions during strengthening"),
    optJson -> Description(General, "Output verification and termination reports to a JSON file"),
    optWatch -> Description(General, "Re-run stainless upon file changes")
  ) ++ MainHelpers.components.map { component =>
    val option = new inox.FlagOptionDef(component.name, false)
    option -> Description(Pipelines, component.description)
  }

  override protected def getCategories = Pipelines +: super.getCategories.filterNot(_ == Pipelines)

  override protected def getDebugSections = super.getDebugSections ++ Set(
    verification.DebugSectionVerification,
    termination.DebugSectionTermination,
    DebugSectionExtraction,
    frontend.DebugSectionFrontend
  )

  override protected def displayVersion(reporter: inox.Reporter) = {
    reporter.title("Stainless verification tool (https://github.com/epfl-lara/stainless)")
  }

  override protected def getName: String = "stainless"

  /* NOTE: Should be implemented by a generated Main class in each compiler-specific project: */
  val factory: frontend.FrontendFactory

  // TODO add (optional) customisation points for CallBacks to access intermediate reports(?)

  def main(args: Array[String]): Unit = try {
    val ctx = setup(args)
    val compilerArgs = args.toList filterNot { _.startsWith("--") }

    val compiler = frontend.run(ctx, compilerArgs, factory)

    // Passively wait until the compiler has finished
    compiler.join()

    // When in "watch" mode, no final report is printed as there is no proper end.
    // In fact, we might not even have a full list of VCs to be checked...
    val watch = ctx.options.findOption(optWatch) getOrElse false

    if (watch) {
      // TODO wrap this in an utility class.

      // Watch each individual file for modification through their parent directories
      // (because a WatchService cannot observe files directly..., also we need to keep
      // track of the modification time because we sometimes receive several event
      // for the same file...)
      val watcher = FileSystems.getDefault.newWatchService()
      val files: Set[File] = compiler.sources.toSet map { file: String => new File(file).getAbsoluteFile }
      val times = MutableMap[File, Long]() ++ (files map { f => f -> f.lastModified })
      val dirs: Set[Path] = files map { _.getParentFile.toPath }
      dirs foreach { _.register(watcher, StandardWatchEventKinds.ENTRY_MODIFY) }

      ctx.reporter.info(s"\n\nWaiting for source changes...\n\n")

      var loop = true

      val interruptible = new inox.utils.Interruptible {
        override def interrupt(): Unit = { loop = false }
      }
      ctx.interruptManager.registerForInterrupts(interruptible)

      while (loop) {
        // Wait for further changes, filtering out everything that is not of interest

        val key = watcher.poll(500, TimeUnit.MILLISECONDS)
        if (key != null) {
          val events = key.pollEvents()
          val notifications = events map { _.context } collect { case p: Path => p.toAbsolutePath.toFile }
          val modified = notifications filter files

          // Update the timestamps while looking for things to process.
          // Note that timestamps are not 100% perfect filters: the files could have the same content.
          // But it's very lightweight and the rest of the pipeline should be able to handle similar
          // content anyway.
          var proceed = false
          for {
            f <- modified
            if f.lastModified > times(f)
          } {
            proceed = true
            times(f) = f.lastModified
          }

          if (proceed) {
            ctx.reporter.info(s"Detecting some file modifications...: ${modified mkString ", "}")
            compiler.run()
            compiler.join()
            ctx.reporter.info(s"\n\nWaiting for source changes...\n\n")
          }

          key.reset()
        }
      }

      ctx.interruptManager.unregisterForInterrupts(interruptible)
      watcher.close()
    } else {
      // Process reports: print summary/export to JSON
      val reports: Seq[AbstractReport] = compiler.getReports
      reports foreach { _.emit(ctx) }

      ctx.options.findOption(optJson) foreach { file =>
        val output = if (file.isEmpty) optJson.default else file
        ctx.reporter.info(s"Outputing JSON summary to $output")
        exportJson(reports, output)
      }
    }

    ctx.reporter.whenDebug(inox.utils.DebugSectionTimers) { debug =>
      ctx.timers.outputTable(debug)
    }

    // Shutdown the pool for a clean exit.
    val unexecuted = MainHelpers.executor.shutdownNow()
    if (unexecuted.size != 0) ctx.reporter.error("Some tasks were not run (" + unexecuted.size + ")")
  } catch {
    case _: inox.FatalError => System.exit(1)
  }

  /** Exports the reports to the given file in JSON format. */
  private def exportJson(reports: Seq[AbstractReport], file: String): Unit = {
    val subs = reports map { r => JObject(r.name -> r.emitJson) }
    val json = if (subs.isEmpty) JObject() else subs reduce { _ ~ _ }
    val string = pretty(render(json))
    val pw = new PrintWriter(new File(file))
    try pw.write(string) finally pw.close()
  }

}

