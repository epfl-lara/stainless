/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

trait VerificationSuite extends ComponentTestSuite {

  override def configurations = super.configurations.map {
    seq => optFailEarly(true) +: seq
  }

  override def ignored = super.ignored ++ Set(
    "verification/valid/Extern1",
    "verification/valid/Extern2",
    "verification/invalid/SpecWithExtern",
    "verification/invalid/BinarySearchTreeQuant"
  )

  val component = VerificationComponent

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

  override def ignored = super.ignored ++ Set(
    // Flaky on smt-z3 for some reason
    "verification/valid/MergeSort2"
  )
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

  override def ignored = super.ignored ++ Set(
    // Flaky on smt-z3 for some reason
    "verification/valid/MergeSort2"
  )
}

class SMTCVC4VerificationSuite extends VerificationSuite {
  override def configurations = super.configurations.map {
    seq => Seq(
      inox.optSelectedSolvers(Set("smt-cvc4")),
      inox.solvers.optCheckModels(true),
      evaluators.optCodeGen(true)
    ) ++ seq
  }

  override def ignored = super.ignored ++ Set(
    // Requires non-linear resonning, unsupported by CVC4
    "verification/valid/Overrides"
  )
}

