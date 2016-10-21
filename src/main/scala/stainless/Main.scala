/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import dotty.tools.dotc._
import dotty.tools.dotc.core.Contexts._

object Main extends inox.MainHelpers {

  override protected def getOptions = super.getOptions ++ Map(
    evaluators.optCodeGen -> "Use code generating evaluator",
    codegen.optInstrumentFields -> "Instrument ADT field access during code generation"
  )

  def main(args: Array[String]): Unit = {
    val inoxCtx = setup(args)
    val compiler = new frontends.dotc.DottyCompiler(inoxCtx)

    val driver = new Driver {
      def newCompiler(implicit ctx: Context) = compiler
    }

    val compilerArgs = args.filterNot(_.startsWith("--")) ++ Build.libraryFiles
    driver.process(compilerArgs)

    val program = compiler.extraction.getProgram
    val structure = compiler.extraction.getStructure

    for (pd <- structure) {
      println(pd.asString(program.printerOpts))
    }
  }
}
