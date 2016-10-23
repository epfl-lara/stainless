/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import dotty.tools.dotc._
import dotty.tools.dotc.core.Contexts._

object Main extends inox.MainHelpers {

  val components: Map[inox.FlagOptionDef, Component] = Map(

  )

  override protected def getOptions = super.getOptions ++ Map(
    evaluators.optCodeGen -> "Use code generating evaluator",
    codegen.optInstrumentFields -> "Instrument ADT field access during code generation"
  )

  def main(args: Array[String]): Unit = {
    val inoxCtx = setup(args)
    val compilerArgs = args.toList.filterNot(_.startsWith("--")) ++ Build.libraryFiles

    val (structure, program) = frontends.scalac.ScalaCompiler(inoxCtx, compilerArgs)

    for (pd <- structure) {
      println(pd.asString(program.printerOpts))
    }
  }
}
