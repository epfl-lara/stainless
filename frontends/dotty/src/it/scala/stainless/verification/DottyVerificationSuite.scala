/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

trait DottyVerificationSuite extends VerificationComponentTestSuite {

  override def configurations = super.configurations.map {
    seq => optFailInvalid(true) +: seq
  }

  override protected def optionsString(options: inox.Options): String = {
    super.optionsString(options) +
    (if (options.findOptionOrDefault(evaluators.optCodeGen)) " codegen" else "")
  }

  def keepOnly(f: String): Boolean = {
    val noLongerCompiles = Set(
      "ConstructorRefinement.scala",
      "IdentityRefinement.scala",
      "PositiveInt.scala",
      "PositiveIntAlias.scala",
      "RefinedTypeMember.scala",
      "SortedListHead.scala",
      "ErasedTerms1.scala"
    )
    noLongerCompiles.forall(s => !f.endsWith(s))
  }

  testPosAll("dotty-specific/valid", keepOnly = keepOnly)

  testNegAll("dotty-specific/invalid")
}

class SMTZ3DottyVerificationSuite extends DottyVerificationSuite {
  override def configurations = super.configurations.map {
    seq => Seq(
      inox.optSelectedSolvers(Set("smt-z3:z3-4.8.12")),
      inox.solvers.optCheckModels(true)
    ) ++ seq
  }
}
