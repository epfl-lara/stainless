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

  import UncheckedSuite._
  testUncheckedAll("verification/unchecked-invalid", uncheckedInvalid._1, uncheckedInvalid._2)
  testUncheckedAll("verification/unchecked-valid", uncheckedValid._1, uncheckedValid._2)
}
object UncheckedSuite {
  private lazy val uncheckedInvalid = ComponentTestSuite.loadPrograms("verification/unchecked-invalid")
  private lazy val uncheckedValid = ComponentTestSuite.loadPrograms("verification/unchecked-valid")
}