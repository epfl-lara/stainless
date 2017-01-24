/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import dotty.tools.dotc._
import dotty.tools.dotc.core.Contexts._

object Main extends inox.MainHelpers {

  val components: Seq[Component] = Seq(
    verification.VerificationComponent,
    termination.TerminationComponent
  )

  case object Pipelines extends Category
  case object Verification extends Category

  override protected def getOptions = super.getOptions ++ Map(
    optFunctions -> Description(General, "Only consider functions s1,s2,..."),
    evaluators.optCodeGen -> Description(Evaluators, "Use code generating evaluator"),
    codegen.optInstrumentFields -> Description(Evaluators, "Instrument ADT field access during code generation"),
    verification.optParallelVCs -> Description(Verification, "Check verification conditions in parallel"),
    verification.optFailEarly -> Description(Verification, "Halt verification as soon as a check fails")
  ) ++ components.map { component =>
    val option = new inox.FlagOptionDef(component.name, false)
    option -> Description(Pipelines, component.description)
  }

  override protected def getCategories = Pipelines +: super.getCategories.filterNot(_ == Pipelines)

  override protected def getDebugSections = super.getDebugSections ++ Set(
    verification.DebugSectionVerification,
    termination.DebugSectionTermination
  )

  override protected def displayVersion(reporter: inox.Reporter) = {
    reporter.title("Stainless verification tool (https://github.com/epfl-lara/stainless)")
  }

  def main(args: Array[String]): Unit = {
    val inoxCtx = setup(args)
    val compilerArgs = Build.libraryFiles ++ args.toList.filterNot(_.startsWith("--"))

    val (structure, program) = frontends.scalac.ScalaCompiler(inoxCtx, compilerArgs)

    val activeComponents = components.filter { c =>
      inoxCtx.options.options.collectFirst {
        case inox.OptionValue(o, value: Boolean) if o.name == c.name => value
      }.getOrElse(false)
    }

    val toExecute = if (activeComponents.isEmpty) {
      Seq(verification.VerificationComponent)
    } else {
      activeComponents
    }

    for (c <- toExecute) c(structure, program).emit()
  }
}
