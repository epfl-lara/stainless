/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

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
    // TODO Once #115 is merged, make Report.stats public and tests this:
    // assert(analysis.toReport.stats.validFromCache == 0, "no cache should be used for this tests")
    for ((vc, vr) <- analysis.vrs) {
      if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
      if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
    }
    reporter.terminateIfError()
  }

  testAll("verification/invalid") { (analysis, _) =>
    val report = analysis.toReport
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

