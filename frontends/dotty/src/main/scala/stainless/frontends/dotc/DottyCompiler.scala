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
    // We also include init.Checker (which happens in the same mini-phase as FirstTransform, therefore not contained in `necessary`)
    necessary :+ List(new init.Checker) :+ List(extractionPhase)
  }

  private class ExtractionPhase extends PluginPhase {
    override val phaseName = "stainless"
    override val runsAfter = Set(Pickler.name)
    override val runsBefore = Set(FirstTransform.name)
    // Note: this must not be instantiated within `run`, because we need the underlying `symbolMapping` in `StainlessExtraction`
    // to be shared across multiple compilation unit.
    val extraction = new StainlessExtraction(ctx)

    override def runOn(units: List[CompilationUnit])(using dottyCtx: DottyContext): List[CompilationUnit] = {
      dottyCtx.reporter match {
        case sr: SimpleReporter if sr.hasSafeInitWarnings =>
          // Do not run the Stainless extraction phase by returning no compilation units
          Nil
        case _ =>
          super.runOn(units)
      }
    }

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
  private var safeInitWarnings: Boolean = false

  private def printMessage(msg: String, pos: inox.utils.Position, severity: Int): Unit = severity match {
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
  private def printMessage(pos: SourcePosition, msg: String, severity: Int): Unit = {
    if (!pos.exists) {
      printMessage(msg, inox.utils.NoPosition, severity)
    } else {
      // Lines and column starts from 0 for Dotty
      val lpos = inox.utils.OffsetPosition(pos.line + 1, pos.column + 1, pos.point, pos.source.file.file)
      printMessage(msg, lpos, severity)
    }
  }

  private def checkSafeInitWarning(msg: String): Boolean = {
    // It seems that we can't extract the type of warning we got, so we have to resort to using questionable practices
    val warn = msg.contains("Access non-initialized") ||
      msg.contains("Promote the value under initialization") ||
      msg.contains("on a value with an unknown initialization") ||
      msg.contains("may cause initialization errors") ||
      msg.contains("Promoting the value to fully-initialized is unsafe")
    safeInitWarnings |= warn
    warn
  }

  def hasSafeInitWarnings: Boolean = safeInitWarnings

  def doReport(dia: Diagnostic)(using DottyContext): Unit = {
    val isSafeInitMsg = dia.level == WARNING && checkSafeInitWarning(dia.msg.message)
    // For -Ysafe-init warning messages, raise the level to error
    val level = if (isSafeInitMsg) ERROR else dia.level
    printMessage(dia.pos, dia.msg.message, level)
  }
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
          val flags = Seq("-color:never", "-language:implicitConversions", "-Ysafe-init", s"-cp:$cps")
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