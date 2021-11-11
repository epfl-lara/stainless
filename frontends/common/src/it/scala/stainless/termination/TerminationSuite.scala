/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package termination

import stainless.utils.YesNoOnly
import stainless.verification.{VerificationComponent, VerificationAnalysis, optFailInvalid, optTypeChecker}

import scala.concurrent.duration._

class TerminationSuite extends ComponentTestSuite {

  override val component: VerificationComponent.type = VerificationComponent

  override def configurations = super.configurations.map { seq =>
    Seq(
      optTypeChecker(true),
      optInferMeasures(true),
      optCheckMeasures(YesNoOnly.Only),
    ) ++ seq
  }

  override protected def optionsString(options: inox.Options): String = {
    "solver=" + options.findOptionOrDefault(inox.optSelectedSolvers).head
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // Cannot prove termination (with either old or new termination checking mechanism)
    case "termination/valid/NNF" => Skip

    // Not compatible with System FR type-checker, or needs more inference
    case "termination/valid/Streams"              => Skip
    case "termination/valid/CyclicFibStream"      => Skip
    case "termination/valid/CyclicHammingStream"  => Skip
    case "termination/valid/Consistent"           => Skip

    // Already correctly rejected by the type-checker
    case "termination/looping/Inconsistency5"           => Skip // ADT Object must appear only in strictly positive positions of Machine
    case "termination/looping/NegativeDatatype"         => Skip // ADT Code must appear only in strictly positive positions of Code
    case "termination/looping/NonStrictPositiveTypes"   => Skip // ADT A must appear only in strictly positive positions of A
    case "termination/looping/NonStrictPositiveTypesIR" => Skip // ADT A must appear only in strictly positive positions of A
    case "termination/looping/Queue"                    => Skip // Call to function looping_2$0 is not allowed here, because it
                                                                // is mutually recursive with the current function looping_1$0

    // Unstable
    case "verification/valid/BigIntMonoidLaws" => Ignore
    case "verification/valid/BigIntRing" => Ignore
    case "verification/valid/InnerClasses4" => Ignore
    case "verification/valid/PropositionalLogic" => Ignore

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
}
