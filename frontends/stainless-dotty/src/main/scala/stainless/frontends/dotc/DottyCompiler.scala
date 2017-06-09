/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.dotc

import dotty.tools.dotc._
import dotty.tools.dotc.typer._
import dotty.tools.dotc.transform._
import dotty.tools.dotc.core.Phases._
import dotty.tools.dotc.core.Contexts._

import extraction.xlang.{trees => xt}

class DottyCompiler(inoxCtx: inox.Context) extends Compiler {

  val extraction = new StainlessExtraction(inoxCtx)

  override def phases: List[List[Phase]] = List(
    List(new FrontEnd),
    List(new PostTyper),
    List(extraction)
  )
}

object DottyCompiler {
  def apply(ctx: inox.Context, compilerOpts: List[String]): (
    List[xt.UnitDef],
    Program { val trees: xt.type }
  ) = {
    implicit val debugSection = DebugSectionExtraction
    val timer = ctx.timers.frontend.start()

    val compiler = new DottyCompiler(ctx)
    val driver = new Driver {
      def newCompiler(implicit ctx: Context) = compiler
    }

    val report = try {
      driver.process(compilerOpts.toArray)
    } catch {
      case e: ImpureCodeEncounteredException =>
        ctx.reporter.debug(s"Extraction failed because of:")
        ctx.reporter.debug(e.pos, e.getMessage, e)
        ctx.reporter.fatalError(e.pos, e.getMessage)
    } finally {
      timer.stop()
    }

    val program = compiler.extraction.getProgram
    val structure = compiler.extraction.getStructure

    if (report.hasErrors) {
      ctx.reporter.fatalError(s"Unable to extract the program because of ${report.errorCount} errors.")
    }

    (structure, program)
  }
}
