/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

class ImperativeSuite extends ComponentTestSuite {

  override def configurations = super.configurations.map {
    seq => optFailEarly(true) +: seq
  }

  override protected def optionsString(options: inox.Options): String = ""

  val component = VerificationComponent

  testAll("imperative/valid") { (report, reporter) =>
    for ((vc, vr) <- report.vrs) {
      if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
      if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
    }
    reporter.terminateIfError()
  }

  testAll("imperative/invalid") { (analysis, _) =>
    val report = analysis.toReport
    assert(report.totalInvalid > 0, "There should be at least one invalid verification condition.")
  }
}
