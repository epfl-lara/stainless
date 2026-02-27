/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

class RefinementSuite extends VerificationComponentTestSuite {

  override protected def optionsString(options: inox.Options): String = ""

  import RefinementSuite._

  testPosAll("refinement/valid", valid)

  testNegAll("refinement/invalid", invalid)
}
object RefinementSuite {
  private lazy val valid = ComponentTestSuite.loadPrograms("refinement/valid")
  private lazy val invalid = ComponentTestSuite.loadPrograms("refinement/invalid")
}