/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import org.scalatest.funspec.AnyFunSpec

import scala.concurrent.Await
import scala.concurrent.duration._

import extraction.ExtractionSummary
import stainless.utils.YesNoOnly

abstract class AbstractLibrarySuite(opts: Seq[inox.OptionValue[?]]) extends AnyFunSpec with InputUtils {
  import ast.SymbolIdentifier

  protected val defaultOptions = Seq(inox.optSelectedSolvers(Set("smt-z3")))

  protected val options = inox.Options(defaultOptions ++ opts)

  protected def symbolName(id: Identifier): String = id match {
    case si: SymbolIdentifier => si.symbol.name
    case id => id.name
  }

  protected def keep(tr: ast.Trees)(fd: tr.FunDef): Boolean = fd match {
    case fd if fd.flags.exists(f => f.name == "unchecked" || f.name == "synthetic") => false
    case fd => true
  }

  describe("stainless library") {
    val ctx: inox.Context = stainless.TestContext(options)
    import ctx.{reporter, given}

    val tryProgram = scala.util.Try(loadFiles(Main.libraryFiles)._2)
    it("should be extractable") {
      assert(tryProgram.isSuccess, "Extraction crashed with exception")
      assert(reporter.errorCount == 0, "Extraction had errors")
    }

    it("should verify") {
      import verification.VerificationComponent
      val run = VerificationComponent.run(extraction.pipeline)
      val exProgram = inox.Program(run.trees)(run.extract(tryProgram.get.symbols)._1)
      assert(reporter.errorCount == 0, "Verification extraction had errors")

      import exProgram.trees._
      val funs = exProgram.symbols.functions.values.filter(keep(exProgram.trees)).map(_.id).toSeq
      val analysis = Await.result(run.execute(funs, exProgram.symbols, ExtractionSummary.NoSummary), Duration.Inf)
      val report = analysis.toReport
      val invalids = analysis.vrs.filter(_._2.isInvalid)
      val inconcls = analysis.vrs.filter(_._2.isInconclusive)
      assert(report.totalConditions == report.totalValid,
        "Only " + report.totalValid + " valid out of " + report.totalConditions + "\n" +
        "Invalids are:\n" + invalids.map(_._1.condition.getPos).mkString("\n") + "\n" +
        "Unknowns are:\n" + inconcls.map(_._1.condition.getPos).mkString("\n"))
    }
  }
}

class LibrarySuite extends AbstractLibrarySuite(Seq(
  termination.optInferMeasures(true),
  termination.optCheckMeasures(YesNoOnly.Yes),
  inox.optTimeout(30.seconds),
))

