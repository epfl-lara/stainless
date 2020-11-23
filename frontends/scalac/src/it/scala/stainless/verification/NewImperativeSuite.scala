/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

class NewImperativeSuite extends ComponentTestSuite with inox.MainHelpers {

  override def configurations = super.configurations.map {
    seq => Seq(extraction.imperative.optNewImperative(true), optFailEarly(true)) ++ seq
  }

  override protected def optionsString(options: inox.Options): String = ""

  val component = VerificationComponent

  testAll("new-imperative/valid") { (report, reporter) =>
    for ((vc, vr) <- report.vrs) {
      if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
      if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
    }
    reporter.terminateIfError()
  }

  testAll("new-imperative/invalid") { (analysis, _) =>
    val report = analysis.toReport
    assert(report.totalInvalid > 0, "There should be at least one invalid verification condition.")
  }
}
