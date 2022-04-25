package stainless
package verification

import scala.util.Try

trait VerificationComponentTestSuite extends ComponentTestSuite { self =>

  override val component: VerificationComponent.type = VerificationComponent

  override def configurations = super.configurations.map { seq =>
    Seq(
      optFailInvalid(true),
      optFailEarly(false)
    ) ++ seq
  }

  def testPosAll(dir: String, recursive: Boolean = false, keepOnly: String => Boolean = _ => true, identifierFilter: Identifier => Boolean = _ => true): Unit =
    testAll(dir, recursive, keepOnly, identifierFilter) { (analysis, reporter, _) =>
      assert(analysis.toReport.stats.validFromCache == 0, "no cache should be used for these tests")
      for ((vc, vr) <- analysis.vrs) {
        if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
        if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
      }
      reporter.terminateIfError()
    }

  def testNegAll(dir: String, recursive: Boolean = false, keepOnly: String => Boolean = _ => true, identifierFilter: Identifier => Boolean = _ => true): Unit =
    testAll(dir, recursive, keepOnly, identifierFilter) { (analysis, reporter, _) =>
      val report = analysis.toReport
      assert(report.totalInvalid > 0, "There should be at least one invalid verification condition. " + report.stats)
    }

  def testUncheckedAll(dir: String, recursive: Boolean = false, keepOnly: String => Boolean = _ => true, identifierFilter: Identifier => Boolean = _ => true): Unit =
    testAll(dir, recursive, keepOnly, identifierFilter) { (analysis, reporter, _) =>
      val report = analysis.toReport
      assert(report.totalInvalid > 0 || report.totalUnknown > 0,
        "There should be at least one invalid/unknown verification condition.")
    }
}