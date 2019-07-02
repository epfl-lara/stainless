/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

trait TypeCheckerSuite extends ComponentTestSuite {

  val component = VerificationComponent
  val cacheAllowed: Boolean

  override def configurations = super.configurations.map {
    seq => optTypeChecker(true) +: optFailInvalid(true) +: seq
  }

  override protected def optionsString(options: inox.Options): String = {
    super.optionsString(options) +
    (if (options.findOptionOrDefault(evaluators.optCodeGen)) " codegen" else "")
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // FIXME: fails in the tests but succeeds on command-line
    case "typechecker/valid/SuperCall5" => Ignore
    case "typechecker/valid/MoreExtendedEuclidGCD" => Ignore

    // FIXME: Indexed recursive types are only supported by the Dotty frontend
    // We could move the type-checker suite to the Dotty tests
    case "typechecker/valid/Streams" => Ignore

    case _ => super.filter(ctx, name)
  }

  testAll("typechecker/valid", true) { (analysis, reporter) =>
    assert(cacheAllowed || analysis.toReport.stats.validFromCache == 0, "no cache should be used for these tests")
    for ((vc, vr) <- analysis.vrs) {
      if (vr.isInvalid) fail(s"The following verification condition was invalid: $vc @${vc.getPos}")
      if (vr.isInconclusive) fail(s"The following verification condition was inconclusive: $vc @${vc.getPos}")
    }
    reporter.terminateIfError()
  }
}

class SMTZ3TypeCheckerSuite extends TypeCheckerSuite {
  override val cacheAllowed = true

  override def configurations = super.configurations.map {
    seq => Seq(
      inox.optSelectedSolvers(Set("smt-z3")),
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
    case "typechecker/valid/BigIntMonoidLaws" => Ignore
    case "typechecker/valid/ConcRope" => Ignore
    case "typechecker/valid/CovariantList" => Ignore
    case "typechecker/valid/Huffman" => Ignore
    case "typechecker/valid/List" => Ignore
    case "typechecker/valid/MoreExtendedEuclidGCD" => Ignore
    case "typechecker/valid/MoreExtendedEuclidReachability" => Ignore
    case "typechecker/valid/Overrides" => Ignore
    case "typechecker/valid/PartialCompiler" => Ignore
    case "typechecker/valid/PartialKVTrace" => Ignore
    case "typechecker/valid/ReachabilityChecker" => Ignore
    case "typechecker/valid/TestPartialFunction" => Ignore
    case "typechecker/valid/TestPartialFunction3" => Ignore
    case _ => super.filter(ctx, name)
  }
}
