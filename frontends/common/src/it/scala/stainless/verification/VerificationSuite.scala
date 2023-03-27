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

class PrincessVerificationSuite extends VerificationSuite {
  override def configurations = super.configurations.map {
    seq => Seq(
      inox.optSelectedSolvers(Set("princess")),
      inox.solvers.optCheckModels(true)
    ) ++ seq
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = name match {
    // valid/MicroTests
    case "verification/valid/ADTWithArray1" => Ignore
    case "verification/valid/ADTWithArray2" => Ignore
    case "verification/valid/ADTWithArray4" => Ignore
    case "verification/valid/ADTWithArray5" => Ignore
    case "verification/valid/ADTWithArray6" => Ignore
    case "verification/valid/Array1" => Ignore
    case "verification/valid/Array2" => Ignore
    case "verification/valid/Array3" => Ignore
    case "verification/valid/Array4" => Ignore
    case "verification/valid/ArrayUpdated" => Ignore
    case "verification/valid/BitVectors2" => Ignore
    case "verification/valid/BitVectors3" => Ignore
    case "verification/valid/Issue803" => Ignore
    case "verification/valid/Monads3" => Ignore
    case "verification/valid/Nested13" => Ignore
    case "verification/valid/SetIsEmpty" => Ignore
    case "verification/valid/Sets1" => Ignore
    case "verification/valid/Sets2" => Ignore
    case "verification/valid/Subtyping1" => Ignore

    // valid/
    case "verification/valid/ArraySlice" => Ignore
    case "verification/valid/AnonymousClasses1" => Ignore
    case "verification/valid/AssociativeList" => Ignore
    case "verification/valid/AmortizedQueue" => Ignore
    case "verification/valid/BalancedParentheses" => Ignore
    case "verification/valid/BasicReal" => Ignore
    case "verification/valid/BinarySearch" => Ignore
    case "verification/valid/BinarySearchTreeQuant" => Ignore
    case "verification/valid/BinarySearchTreeQuant2" => Ignore
    case "verification/valid/BitsTricks" => Ignore
    case "verification/valid/BitsTricksSlow" => Ignore
    case "verification/valid/BooleanOps" => Ignore
    case "verification/valid/BVMaxInterpret" => Ignore
    case "verification/valid/Composition" => Ignore
    case "verification/valid/ConcRope" => Ignore
    case "verification/valid/ConcTree" => Ignore
    case "verification/valid/ContMonad" => Ignore
    case "verification/valid/Count" => Ignore
    case "verification/valid/CovariantList" => Ignore
    case "verification/valid/Filter" => Ignore
    case "verification/valid/FiniteSort" => Ignore
    case "verification/valid/FlatMap" => Ignore
    case "verification/valid/FoolProofAdder" => Ignore
    case "verification/valid/FunctionMaps" => Ignore
    case "verification/valid/FunctionMapsObj" => Ignore
    case "verification/valid/GodelNumbering" => Ignore
    case "verification/valid/Heaps" => Ignore
    case "verification/valid/HOInvocations2" => Ignore
    case "verification/valid/i1379a" => Ignore
    case "verification/valid/i1379e" => Ignore
    case "verification/valid/i1379f" => Ignore
    case "verification/valid/i1379g" => Ignore
    case "verification/valid/InnerClasses4" => Ignore
    case "verification/valid/InnerClassesInvariants" => Ignore
    case "verification/valid/InsertionSort" => Ignore
    case "verification/valid/IntSetInv" => Ignore
    case "verification/valid/Iterables" => Ignore
    case "verification/valid/LawTypeArgsElim" => Ignore
    case "verification/valid/ListMonad" => Ignore
    case "verification/valid/ListOperations" => Ignore
    case "verification/valid/LiteralMaps" => Ignore
    case "verification/valid/Longs" => Ignore
    case "verification/valid/MapDiff" => Ignore
    case "verification/valid/MapGetOrElse2" => Ignore
    case "verification/valid/MapGetPlus" => Ignore
    case "verification/valid/MergeSort" => Ignore
    case "verification/valid/MergeSort2" => Ignore
    case "verification/valid/Monotonicity" => Ignore
    case "verification/valid/NNF" => Ignore
    case "verification/valid/PackedFloat8" => Ignore
    case "verification/valid/ParBalance" => Ignore
    case "verification/valid/PartialCompiler" => Ignore
    case "verification/valid/PartialKVTrace" => Ignore
    case "verification/valid/PositiveMap" => Ignore
    case "verification/valid/PropositionalLogic" => Ignore
    case "verification/valid/QuickSort" => Ignore
    case "verification/valid/QuickSortFilter" => Ignore
    case "verification/valid/RedBlackTree" => Ignore
    case "verification/valid/Reverse" => Ignore
    case "verification/valid/StableSorter" => Ignore
    case "verification/valid/TransitiveQuantification" => Ignore
    case "verification/valid/Trees1" => Ignore
    case "verification/valid/ValueClasses" => Ignore

    // invalid/
    case "verification/invalid/AbstractRefinementMap" => Ignore
    case "verification/invalid/Acc" => Ignore
    case "verification/invalid/AddNaturals1" => Ignore
    case "verification/invalid/AddNaturals2" => Ignore
    case "verification/invalid/ADTWithArray1" => Ignore
    case "verification/invalid/ADTWithArray2" => Ignore
    case "verification/invalid/Array1" => Ignore
    case "verification/invalid/Array2" => Ignore
    case "verification/invalid/Array3" => Ignore
    case "verification/invalid/Array4" => Ignore
    case "verification/invalid/Array5" => Ignore
    case "verification/invalid/Array6" => Ignore
    case "verification/invalid/Array7" => Ignore
    case "verification/invalid/Asserts1" => Ignore
    case "verification/invalid/AssociativityProperties" => Ignore
    case "verification/invalid/BadConcRope" => Ignore
    case "verification/invalid/BigArray" => Ignore
    case "verification/invalid/BinarySearch1" => Ignore
    case "verification/invalid/BinarySearch2" => Ignore
    case "verification/invalid/BinarySearch3" => Ignore
    case "verification/invalid/BraunTree" => Ignore
    case "verification/invalid/Choose1" => Ignore
    case "verification/invalid/Choose2" => Ignore
    case "verification/invalid/Existentials" => Ignore
    case "verification/invalid/ExternFallbackMut" => Ignore
    case "verification/invalid/FiniteSort" => Ignore
    case "verification/invalid/Float8" => Ignore
    case "verification/invalid/ForallAssoc" => Ignore
    case "verification/invalid/HiddenOverride" => Ignore
    case "verification/invalid/HOInvocations" => Ignore
    case "verification/invalid/i497" => Ignore
    case "verification/invalid/i1295" => Ignore
    case "verification/invalid/InductTacticTest" => Ignore
    case "verification/invalid/InsertionSort" => Ignore
    case "verification/invalid/IntSet" => Ignore
    case "verification/invalid/IntSetUnit" => Ignore
    case "verification/invalid/InvisibleOpaque" => Ignore
    case "verification/invalid/Issue1167" => Ignore
    case "verification/invalid/Issue1167b" => Ignore
    case "verification/invalid/LawsExampleInvalid" => Ignore
    case "verification/invalid/ListOperations" => Ignore
    case "verification/invalid/Lists" => Ignore
    case "verification/invalid/Nested15" => Ignore
    case "verification/invalid/PackedFloat8" => Ignore
    case "verification/invalid/PartialSplit" => Ignore
    case "verification/invalid/PositiveMap" => Ignore
    case "verification/invalid/PositiveMap2" => Ignore
    case "verification/invalid/PropositionalLogic" => Ignore
    case "verification/invalid/RedBlackTree" => Ignore
    case "verification/invalid/RedBlackTree2" => Ignore
    case "verification/invalid/SimpleQuantification2" => Ignore
    case "verification/invalid/SpecWithExtern" => Ignore

    // false-valid/ (for greater good...)
    case "verification/false-valid/ForestNothing2" => Ignore

    case _ => super.filter(ctx, name)
  }
}
