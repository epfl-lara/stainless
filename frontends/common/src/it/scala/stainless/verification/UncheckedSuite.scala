/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

class UncheckedSuite extends VerificationComponentTestSuite {
  private val solvers = Seq("smt-z3", "smt-cvc4", "smt-cvc5")

  override def configurations: Seq[Seq[inox.OptionValue[_]]] = {
    solvers.flatMap { solver =>
      super.configurations.map {
        seq => Seq(
          inox.optSelectedSolvers(Set(solver)),
          optFailEarly(true),
          inox.solvers.optCheckModels(false)) ++ seq
      }
    }
  }

  override val component: VerificationComponent.type = VerificationComponent

  testUncheckedAll("verification/unchecked-invalid")
  testUncheckedAll("verification/unchecked-valid")
}
