/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

trait UncheckedSuite extends VerificationComponentTestSuite {

  override def configurations = super.configurations.map {
    seq => Seq(optFailEarly(true), inox.solvers.optCheckModels(false)) ++ seq
  }

  override val component: VerificationComponent.type = VerificationComponent

  testUncheckedAll("verification/unchecked-invalid")
  testUncheckedAll("verification/unchecked-valid")
}

class SMTZ3UncheckedSuite extends UncheckedSuite {
  override def configurations = super.configurations.map {
    seq => inox.optSelectedSolvers(Set("smt-z3:z3-4.8.12")) +: seq
  }
}

class SMTCVC4UncheckedSuite extends UncheckedSuite {
  override def configurations = super.configurations.map {
    seq => inox.optSelectedSolvers(Set("smt-cvc4")) +: seq
  }
}
