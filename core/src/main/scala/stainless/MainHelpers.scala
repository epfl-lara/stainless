/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import extraction.xlang.{trees => xt}

object MainHelpers {
  val components: Seq[Component] = Seq(
    verification.VerificationComponent,
    termination.TerminationComponent
  )
}

trait MainHelpers extends inox.MainHelpers {

  val components = MainHelpers.components

  case object Pipelines extends Category
  case object Verification extends Category
  case object Termination extends Category

  override protected def getOptions = super.getOptions ++ Map(
    optFunctions -> Description(General, "Only consider functions s1,s2,..."),
    evaluators.optCodeGen -> Description(Evaluators, "Use code generating evaluator"),
    codegen.optInstrumentFields -> Description(Evaluators, "Instrument ADT field access during code generation"),
    codegen.optSmallArrays -> Description(Evaluators, "Assume all arrays fit into memory during code generation"),
    verification.optParallelVCs -> Description(Verification, "Check verification conditions in parallel"),
    verification.optFailEarly -> Description(Verification, "Halt verification as soon as a check fails"),
    inox.optTimeout -> Description(General, "Set a timeout n (in sec) such that\n" +
      "  - verification: each proof attempt takes at most n seconds\n" +
      "  - termination: each solver call takes at most n / 100 seconds"),
    termination.optIgnorePosts -> Description(Termination, "Ignore postconditions during termination checking")
  ) ++ MainHelpers.components.map { component =>
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

  override protected def getName: String = "stainless"

  /* NOTE: Should be implemented by a generated Main class in each compiler-specific project: */
  val libraryFiles: List[String]
  def extractFromSource(ctx: inox.Context, compilerOpts: List[String]): (
    List[xt.UnitDef],
    Program { val trees: xt.type }
  )

  def main(args: Array[String]): Unit = try {
    val inoxCtx = setup(args)
    val compilerArgs = libraryFiles ++ args.toList.filterNot(_.startsWith("--"))

    val (structure, program) = extractFromSource(inoxCtx, compilerArgs)

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
  } catch {
    case _: inox.FatalError => System.exit(1)
  }
}
