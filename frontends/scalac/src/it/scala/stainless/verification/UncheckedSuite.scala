/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

trait UncheckedSuite extends ComponentTestSuite {

  override def configurations = super.configurations.map {
    seq => Seq(optFailEarly(true), inox.solvers.optCheckModels(false)) ++ seq
  }

  val component = VerificationComponent

  testAll("verification/unchecked") { (report, _) =>
    assert(report.totalInvalid > 0, "There should be at least one invalid verification condition.")
  }
}

class SMTZ3UncheckedSuite extends UncheckedSuite {
  override def configurations = super.configurations.map {
    seq => inox.optSelectedSolvers(Set("smt-z3")) +: seq
  }
}

class SMTCVC4UncheckedSuite extends UncheckedSuite {
  override def configurations = super.configurations.map {
    seq => inox.optSelectedSolvers(Set("smt-cvc4")) +: seq
  }
}
