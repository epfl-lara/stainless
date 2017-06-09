/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

trait VerificationSuite extends ComponentTestSuite {

  val component = VerificationComponent

  override def configurations = super.configurations.map {
    seq => optFailEarly(true) +: seq
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    case "verification/valid/Extern1" => Ignore
    case "verification/valid/Extern2" => Ignore
    case "verification/valid/ChooseLIA" => Ignore
    case "verification/invalid/SpecWithExtern" => Ignore
    case "verification/invalid/BinarySearchTreeQuant" => Ignore
    case _ => super.filter(ctx, name)
  }

  testAll("verification/valid") { (report, reporter) =>
    for ((vc, vr) <- report.vrs) {
      if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
      if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
    }
    reporter.terminateIfError()
  }

  testAll("verification/invalid") { (report, _) =>
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
    case _ => super.filter(ctx, name)
  }
}

class InlinedPostsVerificationSuite extends VerificationSuite {
  override def configurations = super.configurations.map {
    seq => Seq(
      inox.optSelectedSolvers(Set("smt-z3")),
      inox.solvers.optCheckModels(true),
      extraction.inlining.optInlinePosts(true)
    ) ++ seq
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // Flaky on smt-z3 for some reason
    case "verification/valid/MergeSort2" => Ignore
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

  override protected def optionsString(options: inox.Options): String = {
    super.optionsString(options) + " codegen"
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // Flaky on smt-z3 for some reason
    case "verification/valid/MergeSort2" => Ignore
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
    case _ => super.filter(ctx, name)
  }
}

