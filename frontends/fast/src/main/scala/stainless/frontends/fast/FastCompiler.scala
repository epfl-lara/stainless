package stainless.frontends.fast

import dotty.tools.dotc._
import dotty.tools.dotc.typer._
import dotty.tools.dotc.transform._
import dotty.tools.dotc.core.Phases._
import dotty.tools.dotc.core.Contexts._
import stainless.frontend
import stainless.frontend.{CallBack, Frontend, FrontendFactory, ThreadedFrontend}
import stainless.frontends.dotc.{SymbolsContext}

class FastCompiler(ctx: inox.Context, callback: CallBack, cache: SymbolsContext) extends Compiler {
  override def phases: List[List[Phase]] = List(
    List(new FastParserPhase),
    List(new PostTyper)
  )
}

private class FastDriver(args: Seq[String], compiler: FastCompiler) extends Driver {
  override def newCompiler(implicit ctx: Context) = compiler

  lazy val files = {
    val (files, _) = setup(args.toArray, initCtx)
    files
  }

  def run(): Unit = process(args.toArray)
}


object FastCompiler {

  /** Complying with [[frontend]]'s interface */
  class Factory(
                 override val extraCompilerArguments: Seq[String],
                 override val libraryPaths: Seq[String]
               ) extends FrontendFactory {

    override def apply(ctx: inox.Context, compilerArgs: Seq[String], callback: CallBack): Frontend =
      new ThreadedFrontend(callback, ctx) {

        // Share the same symbols between several runs.
        val cache = new SymbolsContext

        val compiler = new FastCompiler(ctx, callback, cache)
        val args = allCompilerArguments(compilerArgs)

        val driver = new FastDriver(args, compiler)

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

