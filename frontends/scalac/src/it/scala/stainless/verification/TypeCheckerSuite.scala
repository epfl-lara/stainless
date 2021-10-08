/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import scala.concurrent.duration._

import org.scalatest._

trait TypeCheckerSuite extends ComponentTestSuite {

  override val component: VerificationComponent.type = VerificationComponent
  val cacheAllowed: Boolean

  override def configurations = super.configurations.map { seq =>
    Seq(
      optTypeChecker(true),
      optFailInvalid(true),
    ) ++ seq
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // Same as VerificationSuite
    case "verification/valid/Extern1"                 => Ignore
    case "verification/valid/Extern2"                 => Ignore
    case "verification/valid/ChooseLIA"               => Ignore
    case "verification/invalid/SpecWithExtern"        => Ignore
    case "verification/invalid/BinarySearchTreeQuant" => Ignore
    case "verification/invalid/ForallAssoc"           => Ignore

    // unknown/timeout VC but counter-example not found
    case "verification/invalid/BadConcRope"           => Ignore

    // Lemmas used in one equation can leak in other equations due to https://github.com/epfl-lara/inox/issues/139
    case "verification/invalid/Equations1" => Ignore
    case "verification/invalid/Equations2" => Ignore
    case "verification/invalid/Equations3" => Ignore

    // Unstable
    case "verification/valid/BigIntMonoidLaws" => Ignore
    case "verification/valid/BigIntRing" => Ignore
    case "verification/valid/InnerClasses4" => Ignore

    // Not compatible with typechecker
    case "verification/valid/Countable2" => Ignore

    case _ => super.filter(ctx, name)
  }

  testAll("verification/valid", recursive = true) { (analysis, reporter) =>
    assert(cacheAllowed || analysis.toReport.stats.validFromCache == 0, "no cache should be used for these tests")
    for ((vc, vr) <- analysis.vrs) {
      if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
      if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
    }
    reporter.terminateIfError()
  }

  testAll("verification/invalid") { (analysis, _) =>
    val report = analysis.toReport
    assert(report.totalInvalid > 0, "There should be at least one invalid verification condition. " + report.stats)
  }
}

class SMTZ3TypeCheckerSuite extends TypeCheckerSuite {
  override val cacheAllowed = true

  override def configurations = super.configurations.map {
    seq => Seq(
      inox.optSelectedSolvers(Set("smt-z3:z3-4.8.12")),
      inox.solvers.optCheckModels(true),
      verification.optVCCache(true),
    ) ++ seq
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    case _ => super.filter(ctx, name)
  }
}

class SMTCVC4TypeCheckerSuite extends TypeCheckerSuite {
  override val cacheAllowed = true

  override def configurations = super.configurations.map {
    seq => Seq(
      inox.optSelectedSolvers(Set("smt-cvc4")),
      inox.solvers.optCheckModels(true),
      verification.optVCCache(true),
    ) ++ seq
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // Same ignores as SMTCVC4VerificationSuite
    case "verification/valid/ArraySlice" => Ignore
    case "verification/valid/BigIntMonoidLaws" => Ignore
    case "verification/valid/BigIntRing" => Ignore
    case "verification/valid/ConcRope" => Ignore
    case "verification/valid/CovariantList" => Ignore
    case "verification/valid/Huffman" => Ignore
    case "verification/valid/InnerClasses4" => Ignore
    case "verification/valid/Iterables" => Ignore
    case "verification/valid/List" => Ignore
    case "verification/valid/MoreExtendedEuclidGCD" => Ignore
    case "verification/valid/MoreExtendedEuclidReachability" => Ignore
    case "verification/valid/Overrides" => Ignore
    case "verification/valid/PartialCompiler" => Ignore
    case "verification/valid/PartialKVTrace" => Ignore
    case "verification/valid/ReachabilityChecker" => Ignore
    case "verification/valid/TestPartialFunction" => Ignore
    case "verification/valid/TestPartialFunction3" => Ignore

    case _ => super.filter(ctx, name)
  }
}
