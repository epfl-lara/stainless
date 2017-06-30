/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.scalac

import frontend.{ Frontend, FrontendFactory, CallBack }
import scala.tools.nsc.{Global, Settings => NSCSettings, CompilerCommand}
import scala.reflect.internal.Positions

class ScalaCompiler(settings: NSCSettings, ctx: inox.Context, callback: CallBack)
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
      // TODO drop in replacement? add next phases, plus last phase to report VC results
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

  /** Complying with [[frontend]]'s interface */
  class Factory(
    override val extraCompilerArguments: Seq[String],
    override val libraryFiles: Seq[String]
  ) extends FrontendFactory {

    override def apply(ctx: inox.Context, compilerArgs: Seq[String], callback: CallBack): Frontend = {

      val args = allCompilerArguments(compilerArgs)
      val settings = buildSettings(ctx)
      val files = getFiles(args, ctx, settings)

      val instance = new ScalaCompiler(settings, ctx, callback)

      // Implement an interface compatible with MainHelpers. If an exception is thrown from
      // within the compiler, it is rethrown upon stopping of joining.
      // TODO refactor code, maybe, in frontend package if the same code is required for dotty/other frontends
      val compiler = new Frontend(callback) {
        var underlying: instance.Run = null
        var thread: Thread = null
        var exception: Throwable = null

        override def run(): Unit = {
          assert(!isRunning)
          underlying = new instance.Run

          // Run the compiler in the background in order to make the factory
          // non-blocking, and implement a clean stop action.
          val runnable = new Runnable {
            override def run() = try underlying.compile(files) finally underlying = null
          }

          assert(thread == null)
          thread = new Thread(runnable, "stainless compiler")
          thread.setUncaughtExceptionHandler(new Thread.UncaughtExceptionHandler() {
            override def uncaughtException(t: Thread, e: Throwable): Unit = exception = e
          })

          thread.start()
        }

        override def isRunning: Boolean = {
          underlying != null
        }

        override def onStop(): Unit = {
          if (isRunning) {
            underlying.cancel()
            thread.join()
          }

          rethrow()
        }

        override def onJoin(): Unit = {
          if (isRunning) thread.join()

          rethrow()
        }

        private def rethrow(): Unit = if (exception != null) {
          val e = exception
          exception = null
          ctx.reporter.error(s"Rethrowing exception emitted from within the compiler: ${e.getMessage}")
          throw e
        }
      }

      compiler
    }
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

