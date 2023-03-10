/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import scala.concurrent.duration._

import org.scalatest._

trait VerificationSuite extends VerificationComponentTestSuite {

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    case "verification/invalid/ForallAssoc"           => Ignore  // Hangs

    // unknown/timeout VC but counter-example not found
    case "verification/invalid/BadConcRope"           => Ignore

    // Lemmas used in one equation can leak in other equations due to https://github.com/epfl-lara/inox/issues/139
    case "verification/invalid/Equations1" => Ignore
    case "verification/invalid/Equations2" => Ignore
    case "verification/invalid/Equations3" => Ignore

    case _ => super.filter(ctx, name)
  }

  // Scala 2 BitVectors tests leverages the fact that `==` can be used to compare two unrelated types.
  // For instance, if we have x: Int42, then x == 42 is legal.
  // In Scala 3, however, this expression is ill-formed because Int42 and Int (the widened type of 42) are unrelated.
  // Therefore, all BitVectors tests for Scala 3 must perform a conversion for literals
  // (e.g. the above expression is rewritten to x == (42: Int42))
  def bitVectorsTestDiscarding(file: String): Boolean = {
    val scala2BitVectors = Set("MicroTests/scalac/BitVectors1.scala", "MicroTests/scalac/BitVectors2.scala", "MicroTests/scalac/BitVectors3.scala")
    val scala3BitVectors = Set("MicroTests/dotty/BitVectors1.scala", "MicroTests/dotty/BitVectors2.scala", "MicroTests/dotty/BitVectors3.scala")

    (isScala3 || !scala3BitVectors.exists(t => file.endsWith(t))) &&
      (isScala2 || !scala2BitVectors.exists(t => file.endsWith(t)))
  }

  testPosAll("verification/valid", recursive = true, bitVectorsTestDiscarding)

  testNegAll("verification/invalid")

  // Tests that should be rejected, but aren't
  testPosAll("verification/false-valid")
}

class SMTZ3VerificationSuite extends VerificationSuite {
  override def configurations = super.configurations.map {
    seq => Seq(
      inox.optSelectedSolvers(Set("smt-z3:z3-4.8.12")),
      inox.solvers.optCheckModels(true)
    ) ++ seq
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // Flaky
    case "verification/valid/PackedFloat8" => Ignore
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
      inox.solvers.optCheckModels(true)
    ) ++ seq
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
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
