/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import org.scalatest.funsuite.AnyFunSuite
import stainless.utils.YesNoOnly
import stainless.verification._

import scala.concurrent.duration._
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
    case _ => super.filter(ctx, name)
  }

  def getResults(analysis: VerificationAnalysis) = {
    import analysis.program.symbols
    import analysis.program.trees._

    analysis.sources
      .toSeq
      .sortBy(_.name)
      .map(symbols.getFunction(_))
      .map { fd =>
        fd -> fd.flags.collectFirst { case TerminationStatus(status) => status }
      }
  }

  testAll("termination/valid") { (analysis, reporter, _) =>
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

  testAll("verification/valid") { (analysis, reporter, _) =>
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

  testAll("termination/looping") { (analysis, reporter, _) =>
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

  testUncheckedAll("termination/unchecked-invalid")

  // Tests that should be verified, but aren't (not compatible with System FR type-checker, or needs more inference)
  testNegAll("termination/false-invalid")

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

  // Workaround for a compiler crash caused by calling super.test
  def superTest(self: AnyFunSuite, testName: String)(body: => Unit): Unit =
    self.test(testName)(body)
}
