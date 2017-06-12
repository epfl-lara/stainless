/* Copyright 2009-2016 EPFL, Lausanne */

package stainless

import org.scalatest._

class LibrarySuite extends FunSpec {

  describe("stainless library") {
    val reporter = new inox.TestSilentReporter
    val opts = inox.Options(Seq(inox.optSelectedSolvers(Set("smt-z3"))))
    val ctx = inox.Context(reporter, new inox.utils.InterruptManager(reporter), opts)

    val tryProgram = scala.util.Try(Main.extractFromSource(ctx, Main.libraryFiles)._2)
    it("should be extractable") {
      assert(tryProgram.isSuccess, "Extraction crashed with exception")
      assert(reporter.lastErrors.isEmpty, "Extraction had errors")
    }

    it("should verify") {
      import verification.VerificationComponent._
      val exProgram = extract(tryProgram.get)
      assert(reporter.lastErrors.isEmpty, "Verification extraction had errors")

      import exProgram.trees._
      val funs = exProgram.symbols.functions.values.filterNot(_.flags contains Unchecked).map(_.id).toSeq
      val report = apply(funs, exProgram)
      assert(report.totalConditions == report.totalValid,
        "Only " + report.totalValid + " valid out of " + report.totalConditions + "\n" +
        "Invalids are:\n" + report.vrs.filter(_._2.isInvalid).mkString("\n") + "\n" +
        "Unknowns are:\n" + report.vrs.filter(_._2.isInconclusive).mkString("\n"))
    }

    it("should terminate") {
      import termination.TerminationComponent._
      val exProgram = extract(tryProgram.get)
      assert(reporter.lastErrors.isEmpty, "Verification extraction had errors")

      import exProgram.trees._
      val funs = exProgram.symbols.functions.values.filterNot(_.flags contains Unchecked).map(_.id).toSeq
      val report = apply(funs, exProgram)

      assert(report.results.forall(_._2.isGuaranteed),
        "Library functions couldn't be shown terminating:\n" +
        report.results.filterNot(_._2.isGuaranteed).map(p => p._1.id.name -> p._2).mkString("\n"))
    }
  }
}
