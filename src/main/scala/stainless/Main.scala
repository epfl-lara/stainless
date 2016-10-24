/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import dotty.tools.dotc._
import dotty.tools.dotc.core.Contexts._

object Main extends inox.MainHelpers {

  val components: Seq[Component] = Seq(
    verification.VerificationComponent,
    termination.TerminationComponent
  )

  override protected def getOptions = super.getOptions ++ Map(
    optFunctions -> "Only consider functions s1,s2,...",
    evaluators.optCodeGen -> "Use code generating evaluator",
    codegen.optInstrumentFields -> "Instrument ADT field access during code generation",
    verification.optParallelVCs -> "Check verification conditions in parallel"
  ) ++ components.map { component =>
    val option = new inox.FlagOptionDef(component.name, false)
    option -> component.description
  }

  def main(args: Array[String]): Unit = {
    val inoxCtx = setup(args)
    val compilerArgs = args.toList.filterNot(_.startsWith("--")) ++ Build.libraryFiles

    val (structure, program) = frontends.scalac.ScalaCompiler(inoxCtx, compilerArgs)

    for (c <- components) {
      val active = inoxCtx.options.options.collectFirst {
        case inox.OptionValue(o, value: Boolean) if o.name == c.name => value
      }.getOrElse(false)

      if (active) {
        c(structure, program)
      }
    }
  }
}
