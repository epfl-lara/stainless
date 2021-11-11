/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import stainless.utils.YesNoOnly

class TerminationVerificationSuite extends VerificationComponentTestSuite {

  override def configurations = super.configurations.map { seq =>
    Seq(
      optFailInvalid(true),
      verification.optTypeChecker(true),
      termination.optInferMeasures(false),
      termination.optCheckMeasures(YesNoOnly.No),
    ) ++ seq
  }

  override protected def optionsString(options: inox.Options): String = ""

  testPosAll("termination/valid")
}
