/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import stainless.utils.YesNoOnly

class TerminationVerificationSuite extends ComponentTestSuite {

  override val component: VerificationComponent.type = VerificationComponent

  override def configurations = super.configurations.map { seq =>
    Seq(
      optFailInvalid(true),
      verification.optTypeChecker(true),
      termination.optInferMeasures(false),
      termination.optCheckMeasures(YesNoOnly.No),
    ) ++ seq
  }

  override protected def optionsString(options: inox.Options): String = ""

  testAll("termination/valid") { (report, reporter) =>
    for ((vc, vr) <- report.vrs) {
      if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
      if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
    }
    reporter.terminateIfError()
  }
}
