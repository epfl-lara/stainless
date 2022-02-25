/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package frontends.dotc

import dotty.tools.dotc._
import plugins._
import dotty.tools.dotc.reporting.{Diagnostic, Reporter => DottyReporter}
import dotty.tools.dotc.interfaces.Diagnostic.{ERROR, WARNING, INFO}
import dotty.tools.dotc.util.SourcePosition
import dotty.tools.io.AbstractFile
import core.Contexts.{Context => DottyContext, _}
import core.Phases._
import transform._
import typer._
import frontend.{CallBack, Frontend, FrontendFactory, ThreadedFrontend}

import java.io.File
import java.net.URL

class DottyCompiler(ctx: inox.Context, callback: CallBack) extends Compiler {
  override def phases: List[List[Phase]] = {
    val allOrigPhases = super.phases
    val extractionPhase = new ExtractionPhase
    val scheduled = Plugins.schedule(allOrigPhases, List(extractionPhase))
    // We only care about the phases preceding Stainless.
    // We drop the rest as we are not interested in the full compilation pipeline
    // (the whole pipeline is used for StainlessPlugin).
    val necessary = scheduled.takeWhile(_.forall(_.phaseName != extractionPhase.phaseName))
    necessary :+ List(extractionPhase)
  }

  private class ExtractionPhase extends PluginPhase {
    override val phaseName = "stainless"
    override val runsAfter = Set(Pickler.name)
    override val runsBefore = Set(FirstTransform.name)
    // Note: this must not be instantiated within `run`, because we need the underlying `symbolMapping` in `StainlessExtraction`
    // to be shared across multiple compilation unit.
    val extraction = new StainlessExtraction(ctx)

    // This method id called for every compilation unit, and in the same thread.
    override def run(using dottyCtx: DottyContext): Unit =
      extraction.extractUnit.foreach(extracted =>
        callback(extracted.file, extracted.unit, extracted.classes, extracted.functions, extracted.typeDefs))
  }
}

private class DottyDriver(args: Seq[String], compiler: DottyCompiler, reporter: DottyReporter) extends Driver {
  override def newCompiler(using DottyContext) = compiler

  lazy val files: List[String] = setup(args.toArray, initCtx).map(_._1.map(_.path)).getOrElse(Nil)

  def run(): Unit = process(args.toArray, reporter)
}

private class SimpleReporter(val reporter: inox.Reporter) extends DottyReporter {
  final val ERROR_LIMIT = 5

  val count = scala.collection.mutable.Map[Int, Int](
    ERROR   -> 0,
    WARNING -> 0,
    INFO    -> 0,
  )

  def printMessage(msg: String, pos: inox.utils.Position, severity: Int): Unit = severity match {
    case `ERROR` =>
      reporter.error(pos, msg)
    case `WARNING` =>
      reporter.warning(pos, msg)
    case `INFO` =>
      reporter.info(pos, msg)
    case _ =>
      throw new Exception("Severity should be one of ERROR, WARNING, INFO")
  }

  /** Prints the message with the given position indication. */
  def printMessage(pos: SourcePosition, msg: String, severity: Int): Unit = {
    if (!pos.exists) {
      printMessage(msg, inox.utils.NoPosition, severity)
    } else {
      // Lines and column starts from 0 for Dotty
      val lpos = inox.utils.OffsetPosition(pos.line + 1, pos.column + 1, pos.point, pos.source.file.file)
      printMessage(msg, lpos, severity)
    }
  }

  def doReport(dia: Diagnostic)(using DottyContext): Unit = printMessage(dia.pos, dia.msg.message, dia.level)
}

object DottyCompiler {

  /** Complying with [[frontend]]'s interface */
  class Factory(
    override val extraCompilerArguments: Seq[String],
    override val libraryPaths: Seq[String]
  ) extends FrontendFactory {

    override def apply(ctx: inox.Context, compilerArgs: Seq[String], callback: CallBack): Frontend =
      new ThreadedFrontend(callback, ctx) {
        val args = {
          // Attempt to find where the Scala 2.13 and 3.0 libs are.
          // The 3.0 library depends on the 2.13, so we need to fetch the later as well.
          val scala213Lib: String = Option(scala.Predef.getClass.getProtectionDomain.getCodeSource) map {
            x => new File(x.getLocation.toURI).getAbsolutePath
          } getOrElse { ctx.reporter.fatalError("No Scala 2.13 library found.") }
          // NotGiven is only available in Scala 3, so we can be sure that this will give us the Scala 3 library
          // (and not the Scala 2.13 one)
          val scala3Lib: String = Option(scala.util.NotGiven.getClass.getProtectionDomain.getCodeSource) map {
            x => new File(x.getLocation.toURI).getAbsolutePath
          } getOrElse { ctx.reporter.fatalError("No Scala 3 library found.") }

          val cps = Seq(scala213Lib, scala3Lib).distinct.mkString(java.io.File.pathSeparator)
          val flags = Seq("-color:never", "-language:implicitConversions", s"-cp:$cps")
          allCompilerArguments(ctx, compilerArgs) ++ flags
        }
        val compiler: DottyCompiler = new DottyCompiler(ctx, this.callback)

        val driver = new DottyDriver(args, compiler, new SimpleReporter(ctx.reporter))

        override val sources = driver.files

        override def initRun(): Unit = ()

        override def onRun(): Unit = driver.run()

        override def onEnd(): Unit = ()

        override def onStop(thread: Thread): Unit = {
          // TODO implement a graceful stop! Current implementation might not work anyway...
          thread.join()
        }
      }
  }
}