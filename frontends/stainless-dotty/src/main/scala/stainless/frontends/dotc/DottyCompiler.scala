/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.dotc

import dotty.tools.dotc._
import dotty.tools.dotc.typer._
import dotty.tools.dotc.transform._
import dotty.tools.dotc.core.Phases._
import dotty.tools.dotc.core.Contexts._

import frontend.{ Frontend, FrontendFactory, CallBack }

class DottyCompiler(ctx: inox.Context, callback: CallBack) extends Compiler {
  override def phases: List[List[Phase]] = List(
    List(new FrontEnd),
    List(new PostTyper),
    List(new StainlessExtraction(ctx, callback))
  )
}

private class DottyDriver(args: Seq[String], compiler: DottyCompiler) extends Driver {
  override def newCompiler(implicit ctx: Context) = compiler

  lazy val files = {
    val (files, _) = setup(args.toArray, initCtx)
    files
  }

  def run(): Unit = process(args.toArray)
}


object DottyCompiler {

  /** Complying with [[frontend]]'s interface */
  class Factory(
    override val extraCompilerArguments: Seq[String],
    override val libraryFiles: Seq[String]
  ) extends FrontendFactory {

    override def apply(ctx: inox.Context, compilerArgs: Seq[String], callback: CallBack): Frontend = {

      val compiler = new DottyCompiler(ctx, callback)
      val args = allCompilerArguments(compilerArgs)

      val driver = new DottyDriver(args, compiler)

      // FIXME some of this code is duplicated from ScalaCompiler!
      val frontend = new Frontend(callback) {
        var thread: Thread = null
        var exception: Throwable = null

        override val sources = driver.files

        override def run(): Unit = {
          assert(!isRunning)

          // Run the compiler in the background in order to make the factory
          // non-blocking, and implement a clean stop action.
          val runnable = new Runnable {
            override def run() = try {
              callback.beginExtractions()
              driver.run()
            } finally {
              callback.endExtractions()
            }
          }

          thread = new Thread(runnable, "stainless compiler")
          thread.setUncaughtExceptionHandler(new Thread.UncaughtExceptionHandler() {
            override def uncaughtException(t: Thread, e: Throwable): Unit = exception = e
          })

          thread.start()
        }

        override def isRunning: Boolean = thread != null && thread.isAlive

        override def onStop(): Unit = {
          if (isRunning) {
            // TODO implement a graceful stop! Current implementation might not work anyway...
            thread.interrupt()
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

      frontend
    }

  }

}

