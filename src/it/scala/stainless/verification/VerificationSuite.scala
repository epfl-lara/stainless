/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

class VerificationSuite extends ComponentTestSuite with inox.ResourceUtils {

  override val configurations = Seq(
    Seq()
  )

  val component = VerificationComponent

  private case class Output(report: VerificationComponent.VerificationReport, reporter: inox.Reporter)

  protected def mkTests(cat: String)(block: Output => Unit): Unit = {
    val fs = resourceFiles(s"regression/verification/$cat", _.endsWith(".scala")).toList

    val (funss, program) = extract(fs.map(_.getPath))

    for ((name, funs) <- funss) {
      test(name) { ctx =>
        val report = VerificationComponent.apply(funs, program)
        val out = Output(report, program.ctx.reporter)
        block(out)
      }
    }
  }

  protected def testValid() = mkTests("valid") { output =>
    val Output(report, reporter) = output 
    for ((vc, vr) <- report.vrs) {
      if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
      if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
    }
    reporter.terminateIfError()
  }

  protected def testInvalid() = mkTests("invalid") { output =>
    val Output(report, _) = output
    assert(report.totalUnknown === 0, "There should not be unknown verification conditions.")
    assert(report.totalInvalid > 0, "There should be at least one invalid verification condition.")
  }

  protected def testUnknown() = mkTests("unknown") { output =>
    val Output(report, reporter) = output
    for ((vc, vr) <- report.vrs if vr.isInvalid)
      fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
    assert(report.totalUnknown > 0, "There should be at least one unknown verification condition.")
    reporter.terminateIfError()
  }

  protected def testAll() = {
    testValid()
    testInvalid()
    testUnknown()
  }

  override def run(testName: Option[String], args: Args): Status = {
    testAll()
    super.run(testName, args)
  }
}
