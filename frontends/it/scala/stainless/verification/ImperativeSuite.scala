/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

class ImperativeSuite extends ComponentTestSuite {

  override def configurations = super.configurations.map {
    seq => optFailEarly(true) +: seq
  }

  val component = VerificationComponent

  testAll("imperative/valid") { (report, reporter) =>
    for ((vc, vr) <- report.vrs) {
      if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
      if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
    }
    reporter.terminateIfError()
  }

  testAll("imperative/invalid") { (report, _) =>
    assert(report.totalInvalid > 0, "There should be at least one invalid verification condition.")
  }
}
