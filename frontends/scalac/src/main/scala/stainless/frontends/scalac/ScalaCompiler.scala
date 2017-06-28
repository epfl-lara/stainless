/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.scalac

import MainHelpers.{Compiler,CompilerCallBack,CompilerFactory}
import scala.tools.nsc.{Global, Settings => NSCSettings, CompilerCommand}
import scala.reflect.internal.Positions

class ScalaCompiler(settings: NSCSettings, ctx: inox.Context, callback: CompilerCallBack)
  extends Global(settings, new SimpleReporter(settings, ctx.reporter))
     with Positions {

  object stainlessExtraction extends {
    val global: ScalaCompiler.this.type = ScalaCompiler.this
    val runsAfter = List[String]("refchecks")
    val runsRightAfter = None
    val ctx = ScalaCompiler.this.ctx
    val callback = ScalaCompiler.this.callback
  } with StainlessExtraction

  override protected def computeInternalPhases() : Unit = {
    val phs = List(
      syntaxAnalyzer          -> "parse source into ASTs, perform simple desugaring",
      analyzer.namerFactory   -> "resolve names, attach symbols to named trees",
      analyzer.packageObjects -> "load package objects",
      analyzer.typerFactory   -> "the meat and potatoes: type the trees",
      patmat                  -> "translate match expressions",
      superAccessors          -> "add super accessors in traits and nested classes",
      extensionMethods        -> "add extension methods for inline classes",
      pickler                 -> "serialize symbol tables",
      refChecks               -> "reference/override checking, translate nested objects",
      stainlessExtraction     -> "extracts stainless trees out of scala trees"
    )
    phs foreach { phasesSet += _._1 }
  }

  class Run extends super.Run {
    override def progress(current: Int, total: Int) {
      ctx.reporter.onCompilerProgress(current, total)
    }
  }
}

object ScalaCompiler {

  /** Complying with [[MainHelpers.factory]] */
  def factory: CompilerFactory = { case (ctx, compilerArgs, callback) =>

    val settings = buildSettings(ctx)
    val files = getFiles(compilerArgs, ctx, settings)

    val instance = new ScalaCompiler(settings, ctx, callback)

    // Implement an interface compatible with MainHelpers.
    // TODO refactor code, maybe, in MainHelpers if the same code is required for dotty/other frontends
    val compiler = new Compiler(callback) {
      var underlying: instance.Run = null
      var thread: Thread = null

      override def run(): Unit = {
        assert(!isRunning)
        underlying = new instance.Run

        // Run the compiler in the background in order to make the factory
        // non-blocking, and implement a clean stop action.
        val runnable = new Runnable {
          override def run() = try {
            underlying.compile(files)
          } catch {
            case e: Throwable =>
              ctx.reporter.error(s"Got an exception from within the compiler: " + e.getMessage)
              ctx.reporter.error(s"Trace:\n" + (e.getStackTrace mkString "\n"))
              throw e
          } finally {
            underlying = null
          }
        }

        assert(thread == null)
        thread = new Thread(runnable, "stainless compiler")
        thread.start()
      }

      override def isRunning: Boolean = {
        underlying != null
      }

      override def onStop(): Unit = {
        if (isRunning) {
          ctx.reporter.info(s"Stopping compiler...") // TODO make this debug
          val timer = ctx.timers.frontends.cancel.start()
          underlying.cancel()
          thread.join()
          timer.stop()
          ctx.reporter.info(s"Compiler stopped") // TODO make this debug
        }
      }

      override def onJoin(): Unit = {
        if (isRunning) {
          ctx.reporter.info(s"Joining the compiler...") // TODO make this debug
          thread.join()
          ctx.reporter.info(s"Joined!") // TODO make this debug
        }
      }
    }

    compiler
  }

  /** Let the frontend analyse the arguments to understand which files should be compiled. */
  private def getFiles(compilerArgs: Seq[String], ctx: inox.Context, settings: NSCSettings): List[String] = {
    val command = new CompilerCommand(compilerArgs.toList, settings) {
      override val cmdName = "stainless"
    }

    if (!command.ok) { ctx.reporter.fatalError("No input program.") }

    command.files
  }

  /** Build settings for the nsc tools. */
  private def buildSettings(ctx: inox.Context): NSCSettings = {
    val settings = new NSCSettings

    // Attempt to find where the scala lib is.
    val scalaLib: String = Option(scala.Predef.getClass.getProtectionDomain.getCodeSource) map {
      _.getLocation.getPath
    } getOrElse { ctx.reporter.fatalError("No Scala library found.") }

    settings.classpath.value = scalaLib
    settings.usejavacp.value = false
    settings.deprecation.value = true
    settings.Yrangepos.value = true
    settings.skip.value = List("patmat")

    settings
  }

}

