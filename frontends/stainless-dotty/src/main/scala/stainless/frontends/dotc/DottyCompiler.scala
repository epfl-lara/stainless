/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package frontends.dotc

import dotty.tools.dotc._
import dotty.tools.dotc.typer._
import dotty.tools.dotc.transform._
import dotty.tools.dotc.core.Phases._
import dotty.tools.dotc.core.Contexts._

import frontend.{ Frontend, ThreadedFrontend, FrontendFactory, CallBack }

class DottyCompiler(ctx: inox.Context, callback: CallBack, cache: SymbolsContext) extends Compiler {
  override def phases: List[List[Phase]] = List(
    List(new FrontEnd),
    List(new PostTyper),
    List(new StainlessExtraction(ctx, callback, cache))
  )
}

private class DottyDriver(args: Seq[String], compiler: DottyCompiler) extends Driver {
  override def newCompiler(implicit ctx: Context) = compiler

  override protected def doCompile(compiler: Compiler, fileNames: List[String])(implicit ctx: Context) =
    if (fileNames.nonEmpty)
      try {
        val run = compiler.newRun
        run.compile(fileNames)
        run.printSummary()
      }
      catch {
        case ex: dotty.tools.FatalError  =>
          ctx.error(ex.getMessage) // signals that we should fail compilation.
          ctx.reporter
        case ex: Throwable => throw ex
      }
    else ctx.reporter

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
    override val libraryPaths: Seq[String]
  ) extends FrontendFactory {

    override def apply(ctx: inox.Context, compilerArgs: Seq[String], callback: CallBack): Frontend =
      new ThreadedFrontend(callback, ctx) {

        // Share the same symbols between several runs.
        val cache = new SymbolsContext

        val compiler = new DottyCompiler(ctx, callback, cache)

        val flags = Seq("-language:implicitConversions")
        val args = allCompilerArguments(ctx, compilerArgs) ++ flags

        val driver = new DottyDriver(args, compiler)

        override val sources = driver.files

        override def initRun(): Unit = { /* nothing */ }
        override def onRun(): Unit = { driver.run() }
        override def onEnd(): Unit = { /* nothing */ }
        override def onStop(thread: Thread): Unit = {
          // TODO implement a graceful stop! Current implementation might not work anyway...
          thread.interrupt()
        }
      }

  }

}

