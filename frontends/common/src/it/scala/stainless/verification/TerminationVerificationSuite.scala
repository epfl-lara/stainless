/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import stainless.utils.YesNoOnly

class TerminationVerificationSuite extends VerificationComponentTestSuite {

  override def configurations = super.configurations.map { seq =>
    Seq(
      optFailInvalid(true),
      termination.optInferMeasures(false),
      termination.optCheckMeasures(YesNoOnly.No),
    ) ++ seq
  }

  override protected def optionsString(options: inox.Options): String = ""

  import TerminationVerificationSuite._

  testPosAll("termination/valid", valid)
}
object TerminationVerificationSuite {
  private lazy val valid = ComponentTestSuite.loadPrograms("termination/valid")
}