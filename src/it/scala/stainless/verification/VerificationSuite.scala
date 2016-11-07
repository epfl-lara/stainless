/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

class VerificationSuite extends ComponentTestSuite with inox.ResourceUtils {

  override val configurations = Seq(
    Seq(optFailEarly(true))
  )

  val component = VerificationComponent

  private case class Output(report: VerificationComponent.VerificationReport, reporter: inox.Reporter)

  protected def mkTests(cat: String)(block: Output => Unit): Unit = {
    val fs = resourceFiles(s"regression/verification/$cat", _.endsWith(".scala")).toList

    val (funss, program) = extract(fs.map(_.getPath))

    for ((name, funs) <- funss) {
      test(s"$cat/$name") { ctx =>
        val newProgram = program.withContext(ctx)
        val report = VerificationComponent.apply(funs, newProgram)
        val out = Output(report, ctx.reporter)
        block(out)
      }
    }
  }

  mkTests("valid") { output =>
    val Output(report, reporter) = output 
    for ((vc, vr) <- report.vrs) {
      if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
      if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
    }
    reporter.terminateIfError()
  }

  mkTests("invalid") { output =>
    val Output(report, _) = output
    assert(report.totalInvalid > 0, "There should be at least one invalid verification condition.")
  }
}
