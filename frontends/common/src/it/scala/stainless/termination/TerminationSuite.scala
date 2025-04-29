/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import org.scalatest.funsuite.AnyFunSuite
import stainless.utils.YesNoOnly
import stainless.verification.*
import extraction.xlang.trees as xt
import stainless.ComponentTestSuite.LoadedPrograms

import scala.concurrent.duration.*
import scala.util.{Failure, Success, Try}

class TerminationSuite extends VerificationComponentTestSuite {

  override val component: VerificationComponent.type = VerificationComponent

  override def configurations = super.configurations.map { seq =>
    Seq(
      optInferMeasures(true),
      optCheckMeasures(YesNoOnly.Only),
    ) ++ seq
  }

  override protected def optionsString(options: inox.Options): String = {
    "solver=" + options.findOptionOrDefault(inox.optSelectedSolvers).head
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    case "verification/valid/BitsTricksSlow" => Skip
    // Flaky
    case "verification/valid/PackedFloat8" => Ignore
    // Succeeds most of the time, but unsuitable for CI due to its flakiness
    case "imperative/valid/i1306b" => Ignore
    case _ => super.filter(ctx, name)
  }

  def getResults(analysis: VerificationAnalysis) = {
    import analysis.program.symbols
    import analysis.program.trees._

    analysis.sources
      .toSeq
      .sortBy(_.name)
      .map(symbols.getFunction)
      .map { fd =>
        fd -> fd.flags.collectFirst { case TerminationStatus(status) => status }
      }
  }

  import TerminationSuite._

  testAllTerminating("termination/valid", terminationValid)

  testAllTerminating("verification/valid", verificationValid)

  testAllTerminating("imperative/valid", imperativeValid)

  testAll("termination/looping", terminationLooping) { (analysis, reporter, _, _) =>
    import analysis.program.symbols
    import analysis.program.trees._

    val looping = getResults(analysis).filter { case (fd, _) => fd.id.name.startsWith("looping") }
    val notLooping = looping.collect { case (fd, Some(status)) if !status.isNonTerminating => fd }
    assert(notLooping.isEmpty, "Functions " + notLooping.map(_.id) + " should be marked as non-terminating")

    val calling = getResults(analysis).filter { case (fd, _) => fd.id.name.startsWith("calling") }
    val notCalling = calling.collect { case (fd, Some(status)) if !status.isNonTerminating => fd }
    assert(notCalling.isEmpty, "Functions " + notCalling.map(_.id) + " should be marked as non-terminating")

    val guaranteed = getResults(analysis).filter { case (fd, _) => fd.id.name.startsWith("ok") }
    val notGuaranteed = guaranteed.collect { case (fd, Some(status)) if !status.isTerminating => fd }
    assert(notGuaranteed.isEmpty, "Functions " + notGuaranteed.map(_.id) + " should be marked as terminating")

    val mustHaveValidVCs = guaranteed.map(_._1.id)

    for ((vc, vr) <- analysis.vrs if mustHaveValidVCs.contains(vc.fid.id)) {
      if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
      if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
    }
    reporter.terminateIfError()
  }

  testUncheckedAll("termination/unchecked-invalid", terminationUncheckedInvalid)

  // Tests that should be verified, but aren't (not compatible with System FR type-checker, or needs more inference)
  testNegAll("termination/false-invalid", terminationFalseInvalid)

  // Looping programs that are already correctly rejected by the type-checker
  // Since these are rejected at extraction (and not due to invalid VCs), we need
  // do to something akin to ExtractionSuite.
  superTest(this, "termination/rejected should not type-check") {
    given context: inox.Context = createContext(inox.Options(configurations.head))
    val fs = resourceFiles("termination/rejected", _.endsWith(".scala")).toList map { _.getPath }
    val tryPrograms = fs.map { f =>
      f -> Try {
        val program = loadFiles(List(f))._2
        val programSymbols = frontend.UserFiltering().transform(program.symbols)
        val exSyms = component.run(extraction.pipeline).extract(programSymbols)._1

        val p = inox.Program(stainless.trees)(exSyms)
        val assertions = AssertionInjector(p, context)
        val assertionEncoder = inox.transformers.ProgramEncoder(p)(assertions)

        TypeChecker(assertionEncoder.targetProgram, context).checkFunctionsAndADTs(Seq.empty)
      }
    }

    tryPrograms.foreach { case (f, tp) => tp match {
      case Failure(_) => ()
      case Success(_) => fail(s"$f was successfully extracted")
    }}
  }

  private def testAllTerminating(dir: String, lp: LoadedPrograms): Unit = {
    testAll(dir, lp) { (analysis, reporter, _, _) =>
      val failures = getResults(analysis).collect {
        case (fd, Some(status)) if !status.isTerminating => fd
      }

      assert(failures.isEmpty, "Functions " + failures.map(_.id) + " should be annotated as terminating")

      for ((vc, vr) <- analysis.vrs) {
        if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
        if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
      }
      reporter.terminateIfError()
    }
  }

  // Workaround for a compiler crash caused by calling super.test
  def superTest(self: AnyFunSuite, testName: String)(body: => Unit): Unit =
    self.test(testName)(body)
}
object TerminationSuite {
  private lazy val terminationValid = ComponentTestSuite.loadPrograms("termination/valid")
  private lazy val verificationValid = ComponentTestSuite.loadPrograms("verification/valid")
  private lazy val imperativeValid = ComponentTestSuite.loadPrograms("imperative/valid")
  private lazy val terminationLooping = ComponentTestSuite.loadPrograms("termination/looping")
  private lazy val terminationUncheckedInvalid = ComponentTestSuite.loadPrograms("termination/unchecked-invalid")
  private lazy val terminationFalseInvalid = ComponentTestSuite.loadPrograms("termination/false-invalid")
}