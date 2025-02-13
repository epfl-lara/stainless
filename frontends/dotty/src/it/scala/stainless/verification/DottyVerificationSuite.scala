/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

class DottyVerificationSuite extends VerificationComponentTestSuite {

  override protected def optionsString(options: inox.Options): String = ""

  import DottyVerificationSuite._

  testPosAll("dotty-specific/valid", valid)

  testNegAll("dotty-specific/invalid", invalid)
}
object DottyVerificationSuite {
  private def keepOnly(f: String): Boolean = {
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
  private lazy val valid = ComponentTestSuite.loadPrograms("dotty-specific/valid", keepOnly = keepOnly)
  private lazy val invalid = ComponentTestSuite.loadPrograms("dotty-specific/invalid")
}