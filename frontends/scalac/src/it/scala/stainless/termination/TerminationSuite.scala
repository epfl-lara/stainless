/* Copyright 2009-2019 EPFL, Lausanne */

package stainless
package termination

import stainless.utils.YesNoOnly
import stainless.verification.{VerificationComponent, VerificationAnalysis, optFailInvalid, optTypeChecker}
import stainless.extraction.termination.{optIgnorePosts, optInferMeasures, optCheckMeasures}

import scala.concurrent.duration._

class TerminationSuite extends ComponentTestSuite {

  val component = VerificationComponent

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

    // Not compatible with System FR type-checker
    case "termination/valid/Streams" => Skip

    // smt-z3 crashes on some permutations of the MergeSort2 problem encoding due to Bags...
    // case "verification/valid/MergeSort2" => WithContext(ctx.copy(options = ctx.options + optIgnorePosts(true)))

    // Relation processor hangs when strengthening applications (TODO: open issue and link it here)
    case "verification/valid/LawTypeArgsElim" => Skip
    case "verification/valid/QuickSortFilter" => Skip
    case "verification/valid/StableSorter" => Skip

    // Invalid measure inferred in ChainProcessor
    case "termination/valid/BottomUpMergeSort" => Skip

    // Invalid measure inferred in RelationProcessor
    case "termination/valid/HOTermination" => Skip
    case "termination/valid/Indirect" => Skip
    case "termination/valid/QuickSort" => Skip
    case "verification/valid/MergeSort" => Skip
    case "verification/valid/MergeSort2" => Skip

    // Fails due to a bug in ChainProcessor
    case "verification/valid/Nested14" => Skip
    case "verification/valid/Nested16" => Skip

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

  testAll("termination/valid") { (analysis, reporter) =>
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

  testAll("verification/valid") { (analysis, reporter) =>
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

  // testAll("termination/looping") { (analysis, reporter) =>
  //   import analysis.program.symbols
  //   import analysis.program.trees._

  //   val looping = getResults(analysis).filter { case (fd, _) => fd.id.name.startsWith("looping") }
  //   val notLooping = looping.collect { case (fd, Some(status)) if !status.isNonTerminating => fd }
  //   assert(notLooping.isEmpty, "Functions " + notLooping.map(_.id) + " should be marked as non-terminating")

  //   val calling = getResults(analysis).filter { case (fd, _) => fd.id.name.startsWith("calling") }
  //   val notCalling = calling.collect { case (fd, Some(status)) if !status.isNonTerminating => fd }
  //   assert(notCalling.isEmpty, "Functions " + notCalling.map(_.id) + " should be marked as non-terminating")

  //   val guaranteed = getResults(analysis).filter { case (fd, _) => fd.id.name.startsWith("ok") }
  //   val notGuaranteed = guaranteed.collect { case (fd, Some(status)) if !status.isTerminating => fd }
  //   assert(notGuaranteed.isEmpty, "Functions " + notGuaranteed.map(_.id) + " should be marked as terminating")

  //   val mustHaveValidVCs = guaranteed.map(_._1.id)

  //   for ((vc, vr) <- analysis.vrs if mustHaveValidVCs.contains(vc.fd.id)) {
  //     if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
  //     if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
  //   }
  //   reporter.terminateIfError()
  // }
}
