package stainless
package verification

import scala.util.Try
import extraction.xlang.{trees => xt}

trait VerificationComponentTestSuite extends ComponentTestSuite { self =>

  override val component: VerificationComponent.type = VerificationComponent

  override def configurations = super.configurations.map { seq =>
    Seq(
      optFailInvalid(true),
      optFailEarly(false)
    ) ++ seq
  }

  def testPosAll(dir: String, structure: Seq[xt.UnitDef], programSymbols: xt.Symbols, identifierFilter: Identifier => Boolean = _ => true): Unit =
    testAll(dir, structure, programSymbols, identifierFilter) { (analysis, reporter, _) =>
      assert(analysis.toReport.stats.validFromCache == 0, "no cache should be used for these tests")
      for ((vc, vr) <- analysis.vrs) {
        if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
        if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
      }
      reporter.terminateIfError()
    }

  def testNegAll(dir: String, structure: Seq[xt.UnitDef], programSymbols: xt.Symbols, identifierFilter: Identifier => Boolean = _ => true): Unit =
    testAll(dir, structure, programSymbols, identifierFilter) { (analysis, reporter, _) =>
      val report = analysis.toReport
      assert(report.totalInvalid > 0, "There should be at least one invalid verification condition. " + report.stats)
    }

  def testUncheckedAll(dir: String, structure: Seq[xt.UnitDef], programSymbols: xt.Symbols, identifierFilter: Identifier => Boolean = _ => true): Unit =
    testAll(dir, structure, programSymbols, identifierFilter) { (analysis, reporter, _) =>
      val report = analysis.toReport
      assert(report.totalInvalid > 0 || report.totalUnknown > 0,
        "There should be at least one invalid/unknown verification condition.")
    }
}