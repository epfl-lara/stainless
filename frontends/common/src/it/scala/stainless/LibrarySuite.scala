/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import org.scalatest.funspec.AnyFunSpec

import scala.concurrent.Await
import scala.concurrent.duration._

import stainless.utils.YesNoOnly

abstract class AbstractLibrarySuite(opts: Seq[inox.OptionValue[_]]) extends AnyFunSpec with InputUtils {
  import ast.SymbolIdentifier

  protected val defaultOptions = Seq(inox.optSelectedSolvers(Set("smt-z3")))

  protected val options = inox.Options(defaultOptions ++ opts)

  protected def symbolName(id: Identifier): String = id match {
    case si: SymbolIdentifier => si.symbol.name
    case id => id.name
  }

  protected def keep(tr: ast.Trees)(fd: tr.FunDef): Boolean = fd match {
    case fd if fd.flags.exists(_.name == "unchecked") => false
    case fd => true
  }

  describe("stainless library") {
    val ctx: inox.Context = stainless.TestContext(options)
    import ctx.{reporter, given}

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
      val funs = exProgram.symbols.functions.values.filter(keep(exProgram.trees)).map(_.id).toSeq
      val analysis = Await.result(run.execute(funs, exProgram.symbols), Duration.Inf)
      val report = analysis.toReport
      assert(report.totalConditions == report.totalValid,
        "Only " + report.totalValid + " valid out of " + report.totalConditions + "\n" +
        "Invalids are:\n" + analysis.vrs.filter(_._2.isInvalid).mkString("\n") + "\n" +
        "Unknowns are:\n" + analysis.vrs.filter(_._2.isInconclusive).mkString("\n"))
    }
  }
}

class LibrarySuite extends AbstractLibrarySuite(Seq(
  verification.optTypeChecker(false)
))

class TypeCheckerLibrarySuite extends AbstractLibrarySuite(Seq(
  verification.optTypeChecker(true),
  termination.optInferMeasures(true),
  termination.optCheckMeasures(YesNoOnly.Yes),
))

