/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import org.scalatest._

trait VerificationSuite extends VerificationComponentTestSuite {

  override def configurations = super.configurations.map { seq =>
    Seq(optTypeChecker(false)) ++ seq
  }

  override protected def optionsString(options: inox.Options): String = {
    super.optionsString(options) +
    (if (options.findOptionOrDefault(evaluators.optCodeGen)) " codegen" else "")
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    case "verification/valid/Extern1" => Ignore
    case "verification/valid/Extern2" => Ignore
    case "verification/valid/ChooseLIA" => Ignore
    case "verification/valid/Streams" => Ignore // only for TypeCheckerSuite
    case "verification/invalid/SpecWithExtern" => Ignore
    case "verification/invalid/BinarySearchTreeQuant" => Ignore
    case "verification/invalid/ForallAssoc" => Ignore

    // Lemmas used in one equation can leak in other equations due to https://github.com/epfl-lara/inox/issues/139
    case "verification/invalid/Equations1" => Ignore
    case "verification/invalid/Equations2" => Ignore
    case "verification/invalid/Equations3" => Ignore

    // Unstable
    case "verification/valid/BigIntMonoidLaws" => Ignore
    case "verification/valid/BigIntRing" => Ignore
    case "verification/valid/InnerClasses4" => Ignore
    case "verification/valid/PropositionalLogic" => Ignore

    case _ => super.filter(ctx, name)
  }

  testPosAll("verification/valid")

  testNegAll("verification/invalid")
}

class SMTZ3VerificationSuite extends VerificationSuite {
  override def configurations = super.configurations.map {
    seq => Seq(
      inox.optSelectedSolvers(Set("smt-z3:z3-4.8.12")),
      inox.solvers.optCheckModels(true)
    ) ++ seq
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // Flaky on smt-z3 for some reason
    case "verification/valid/MergeSort2" => Ignore
    case "verification/valid/IntSetInv" => Ignore

    // Too slow on smt-z3, even for nightly build
    case "verification/valid/BitsTricksSlow" => Skip

    case _ => super.filter(ctx, name)
  }
}

class CodeGenVerificationSuite extends SMTZ3VerificationSuite {
  override def configurations = super.configurations.map {
    seq => Seq(
      inox.solvers.unrolling.optFeelingLucky(true),
      inox.solvers.optCheckModels(true),
      evaluators.optCodeGen(true)
    ) ++ seq
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // Does not work with --feeling-lucky. See #490
    case "verification/valid/MsgQueue" => Skip

    // assertion failed in `compileLambda`
    case "verification/valid/GodelNumbering" => Ignore

    case _ => super.filter(ctx, name)
  }
}

class SMTCVC4VerificationSuite extends VerificationSuite {
  override def configurations = super.configurations.map {
    seq => Seq(
      inox.optSelectedSolvers(Set("smt-cvc4")),
      inox.solvers.optCheckModels(true),
      evaluators.optCodeGen(true)
    ) ++ seq
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // Requires non-linear resonning, unsupported by CVC4
    case "verification/valid/Overrides" => Ignore
    case "verification/valid/TestPartialFunction" => Ignore
    case "verification/valid/TestPartialFunction3" => Ignore
    case "verification/valid/BigIntRing" => Ignore
    case "verification/valid/BigIntMonoidLaws" => Ignore
    case "verification/valid/InnerClasses4" => Ignore

    // assertion failed in `compileLambda`
    case "verification/valid/GodelNumbering" => Ignore

    // This test is flaky on CVC4
    case "verification/valid/CovariantList" => Ignore

    // Requires map with non-default values, unsupported by CVC4
    case "verification/valid/ArraySlice" => Ignore
    case "verification/valid/Iterables" => Ignore

    // These tests are too slow on CVC4 and make the regression unstable
    case "verification/valid/ConcRope" => Ignore
    case "verification/invalid/BadConcRope" => Ignore

    // These tests make CVC4 crash
    case "verification/valid/PartialCompiler" => Ignore
    case "verification/valid/PartialKVTrace" => Ignore

    // Codegen assertion error, unsupported by CVC4
    // => Ignored until #681 fixed
    case "verification/invalid/BodyEnsuring" => Ignore

    case _ => super.filter(ctx, name)
  }
}
