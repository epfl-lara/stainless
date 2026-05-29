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

class RefinementSuitePartial extends VerificationComponentTestSuite {

  override protected def optionsString(options: inox.Options): String = 
    "check-measures=false infer-measures=false strict-arithmetic=false"

  import RefinementSuite._

  testPosAll("refinement/valid-partial", partial)
}

object RefinementSuite {
  private lazy val valid = ComponentTestSuite.loadPrograms("refinement/valid")
  lazy val partial = ComponentTestSuite.loadPrograms("refinement/valid-partial")
  private lazy val invalid = ComponentTestSuite.loadPrograms("refinement/invalid")
}