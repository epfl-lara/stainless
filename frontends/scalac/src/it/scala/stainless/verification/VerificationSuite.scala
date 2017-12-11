/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

/*
 * A special test for --functions=therorem --check-models.
 *
 * The goal is to tests the combination of the Registry
 * and the VerificationComponent under these options.
 */
class RegistryVerificationSuite extends ComponentTestSuite {

  val component = VerificationComponent

  override def configurations = super.configurations.map {
    seq => inox.solvers.optCheckModels(true) +: optFunctions("theorem" :: Nil) +: seq
  }

  test(s"special --functions=theorem --check-models test", ctx => filter(ctx, "")) { ctx =>
    val fs = resourceFiles("extraction/registry", _.endsWith(".scala"))
    assert(fs.size == 1 && fs.head.getName == "TestFunctionsOption.scala", "Test files were changed!")
    val Seq(file) = fs

    val (uName, funs, program) = extractOne(file.getPath, ctx, useFilter = true)
    assert(uName == "TestFunctionsOption")
    val analysis = component.apply(funs, program, ctx)
    val stats = analysis.toReport.stats

    // analysis.vrs foreach { r => info(r.toString) }

    assert(stats.valid   == 0, "No VC is expected to be valid for this test.")
    assert(stats.unknown == 0, "No VC is expected to be unknown for this test.")
    assert(stats.invalid == 1, "Exactly one VC is expected to be invalid for this test.")
  }
}

trait VerificationSuite extends ComponentTestSuite {

  val component = VerificationComponent

  override def configurations = super.configurations.map {
    seq => optFailEarly(true) +: seq
  }

  override protected def optionsString(options: inox.Options): String = {
    super.optionsString(options) +
    (if (options.findOptionOrDefault(evaluators.optCodeGen)) " codegen" else "")
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    case "verification/valid/Extern1" => Ignore
    case "verification/valid/Extern2" => Ignore
    case "verification/valid/ChooseLIA" => Ignore
    case "verification/invalid/SpecWithExtern" => Ignore
    case "verification/invalid/BinarySearchTreeQuant" => Ignore
    case _ => super.filter(ctx, name)
  }

  testAll("verification/valid") { (analysis, reporter) =>
    val report = analysis.toReport
    for ((vc, vr) <- analysis.vrs) {
      if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
      if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
    }
    reporter.terminateIfError()
  }

  testAll("verification/invalid") { (analysis, _) =>
    val report = analysis.toReport
    assert(report.totalUnknown == 0, "No VC should be inconclusive")
    assert(report.totalInvalid > 0, "There should be at least one invalid verification condition.")
  }
}

class SMTZ3VerificationSuite extends VerificationSuite {
  override def configurations = super.configurations.map {
    seq => Seq(
      inox.optSelectedSolvers(Set("smt-z3")),
      inox.solvers.optCheckModels(true)
    ) ++ seq
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // Flaky on smt-z3 for some reason
    case "verification/valid/MergeSort2" => Ignore
    case "verification/valid/IntSetInv" => Ignore
    case _ => super.filter(ctx, name)
  }
}

class CodeGenVerificationSuite extends VerificationSuite {
  override def configurations = super.configurations.map {
    seq => Seq(
      inox.optSelectedSolvers(Set("smt-z3")),
      inox.solvers.unrolling.optFeelingLucky(true),
      inox.solvers.optCheckModels(true),
      evaluators.optCodeGen(true)
    ) ++ seq
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // Flaky on smt-z3 for some reason
    case "verification/valid/MergeSort2" => Ignore
    case "verification/valid/IntSetInv" => Ignore
    case _ => super.filter(ctx, name)
  }
}

class SMTCVC4VerificationSuite extends VerificationSuite {
  override def configurations = super.configurations.map {
    seq => Seq(
      inox.optSelectedSolvers(Set("smt-cvc4")),
      inox.solvers.optCheckModels(true),
      evaluators.optCodeGen(true)
    ) ++ seq
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // Requires non-linear resonning, unsupported by CVC4
    case "verification/valid/Overrides" => Ignore
    case "verification/invalid/Existentials" => Ignore
    // These tests are too slow on CVC4 and make the regression unstable
    case "verification/valid/ConcRope" => Ignore
    case "verification/invalid/BadConcRope" => Ignore
    case _ => super.filter(ctx, name)
  }
}

