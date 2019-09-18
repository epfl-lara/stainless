/* Copyright 2009-2019 EPFL, Lausanne */

package stainless

import org.scalatest._

import scala.concurrent.Await
import scala.concurrent.duration._

class LibrarySuite extends FunSpec with InputUtils {

  describe("stainless library") {
    val opts = inox.Options(Seq(inox.optSelectedSolvers(Set("smt-z3"))))
    implicit val ctx = stainless.TestContext(opts)
    import ctx.reporter

    val tryProgram = scala.util.Try(loadFiles(Seq.empty)._2)
    it("should be extractable") {
      assert(tryProgram.isSuccess, "Extraction crashed with exception")
      assert(reporter.errorCount == 0, "Extraction had errors")
    }

    it("should verify") {
      import verification.VerificationComponent
      val run = VerificationComponent.run(extraction.pipeline)
      val exProgram = inox.Program(run.trees)(run extract tryProgram.get.symbols)
      assert(reporter.errorCount == 0, "Verification extraction had errors")

      import exProgram.trees._
      val funs = exProgram.symbols.functions.values.filterNot(_.flags contains Unchecked).map(_.id).toSeq
      val analysis = Await.result(run.execute(funs, exProgram.symbols), Duration.Inf)
      val report = analysis.toReport
      assert(report.totalConditions == report.totalValid,
        "Only " + report.totalValid + " valid out of " + report.totalConditions + "\n" +
        "Invalids are:\n" + analysis.vrs.filter(_._2.isInvalid).mkString("\n") + "\n" +
        "Unknowns are:\n" + analysis.vrs.filter(_._2.isInconclusive).mkString("\n"))
    }

    it("should terminate") {
      import termination.TerminationComponent
      val run = TerminationComponent.run(extraction.pipeline)
      val exProgram = inox.Program(run.trees)(run extract tryProgram.get.symbols)
      assert(reporter.errorCount == 0, "Verification extraction had errors")

      import exProgram.trees._
      val funs = exProgram.symbols.functions.values.filterNot(_.flags contains Unchecked).map(_.id).toSeq
      val analysis = Await.result(run.execute(funs, exProgram.symbols), Duration.Inf)

      assert(
        analysis.results forall { case (_, (g, _)) => g.isGuaranteed },
        "Library functions couldn't be shown terminating:\n" +
        (analysis.results collect { case (fd, (g, _)) if !g.isGuaranteed => fd.id.name -> g } mkString "\n")
      )
    }
  }
}
