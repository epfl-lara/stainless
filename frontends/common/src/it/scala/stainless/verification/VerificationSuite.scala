/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import scala.concurrent.duration._

import org.scalatest._

class VerificationSuite extends VerificationComponentTestSuite {
  private val solvers = Seq("smt-z3", "smt-cvc5", "princess")

  private val ignoreCommon = Set(
    // Hangs
    "verification/invalid/ForallAssoc",
    // unknown/timeout VC but counter-example not found
    "verification/invalid/BadConcRope",
    // Lemmas used in one equation can leak in other equations due to https://github.com/epfl-lara/inox/issues/139
    "verification/invalid/Equations1",
    "verification/invalid/Equations2",
    "verification/invalid/Equations3",
  )

  private val ignoreZ3 = ignoreCommon ++
    Set(
      // Flaky
      "verification/valid/PackedFloat8",
    )

  private val ignoreCVC = ignoreCommon ++
    Set(
      // Unknown / cannot encode map with non-default values
      "verification/valid/ArraySlice",
      "verification/valid/BigIntMonoidLaws",
      "verification/valid/BigIntRing",
      "verification/valid/InnerClasses4",
      "verification/valid/Iterables",
      "verification/valid/PartialCompiler",
      "verification/valid/PartialKVTrace",
    )

  private val ignorePrincess = ignoreCommon ++
    Set(
      // valid/MicroTests
      "verification/valid/ADTWithArray1",
      "verification/valid/ADTWithArray2",
      "verification/valid/ADTWithArray4",
      "verification/valid/ADTWithArray5",
      "verification/valid/ADTWithArray6",
      "verification/valid/Array1",
      "verification/valid/Array2",
      "verification/valid/Array3",
      "verification/valid/Array4",
      "verification/valid/ArrayUpdated",
      "verification/valid/BitVectors2",
      "verification/valid/BitVectors3",
      "verification/valid/Issue803",
      "verification/valid/Monads3",
      "verification/valid/Nested13",
      "verification/valid/SetIsEmpty",
      "verification/valid/Sets1",
      "verification/valid/Sets2",
      "verification/valid/Subtyping1",

      // valid/
      "verification/valid/ArraySlice",
      "verification/valid/AnonymousClasses1",
      "verification/valid/AssociativeList",
      "verification/valid/AmortizedQueue",
      "verification/valid/BalancedParentheses",
      "verification/valid/BasicReal",
      "verification/valid/BinarySearch",
      "verification/valid/BinarySearchTreeQuant",
      "verification/valid/BinarySearchTreeQuant2",
      "verification/valid/BitsTricks",
      "verification/valid/BitsTricksSlow",
      "verification/valid/BooleanOps",
      "verification/valid/BVMaxInterpret",
      "verification/valid/Composition",
      "verification/valid/ConcRope",
      "verification/valid/ConcTree",
      "verification/valid/ContMonad",
      "verification/valid/Count",
      "verification/valid/CovCollection",
      "verification/valid/Filter",
      "verification/valid/FiniteSort",
      "verification/valid/FlatMap",
      "verification/valid/FoolProofAdder",
      "verification/valid/FunctionMaps",
      "verification/valid/FunctionMapsObj",
      "verification/valid/GodelNumbering",
      "verification/valid/Heaps",
      "verification/valid/HOInvocations2",
      "verification/valid/i1379a",
      "verification/valid/i1379e",
      "verification/valid/i1379f",
      "verification/valid/i1379g",
      "verification/valid/InnerClasses4",
      "verification/valid/InnerClassesInvariants",
      "verification/valid/InsertionSort",
      "verification/valid/IntSetInv",
      "verification/valid/Iterables",
      "verification/valid/LawTypeArgsElim",
      "verification/valid/LeanMergeSort",
      "verification/valid/ListMonad",
      "verification/valid/ListOperations",
      "verification/valid/LiteralMaps",
      "verification/valid/Longs",
      "verification/valid/MapDiff",
      "verification/valid/MapGetOrElse2",
      "verification/valid/MapGetPlus",
      "verification/valid/MergeSort",
      "verification/valid/MergeSort2",
      "verification/valid/Monotonicity",
      "verification/valid/NNF",
      "verification/valid/PackedFloat8",
      "verification/valid/ParBalance",
      "verification/valid/PartialCompiler",
      "verification/valid/PartialKVTrace",
      "verification/valid/PositiveMap",
      "verification/valid/PropositionalLogic",
      "verification/valid/QuickSort",
      "verification/valid/QuickSortFilter",
      "verification/valid/RedBlackTree",
      "verification/valid/Reverse",
      "verification/valid/StableSorter",
      "verification/valid/TransitiveQuantification",
      "verification/valid/Trees1",
      "verification/valid/ValueClasses",

      // invalid/
      "verification/invalid/AbstractRefinementMap",
      "verification/invalid/Acc",
      "verification/invalid/AddNaturals1",
      "verification/invalid/AddNaturals2",
      "verification/invalid/ADTWithArray1",
      "verification/invalid/ADTWithArray2",
      "verification/invalid/Array1",
      "verification/invalid/Array2",
      "verification/invalid/Array3",
      "verification/invalid/Array4",
      "verification/invalid/Array5",
      "verification/invalid/Array6",
      "verification/invalid/Array7",
      "verification/invalid/Asserts1",
      "verification/invalid/AssociativityProperties",
      "verification/invalid/BadConcRope",
      "verification/invalid/BigArray",
      "verification/invalid/BinarySearch1",
      "verification/invalid/BinarySearch2",
      "verification/invalid/BinarySearch3",
      "verification/invalid/BraunTree",
      "verification/invalid/Choose1",
      "verification/invalid/Choose2",
      "verification/invalid/Existentials",
      "verification/invalid/ExternFallbackMut",
      "verification/invalid/FiniteSort",
      "verification/invalid/Float8",
      "verification/invalid/ForallAssoc",
      "verification/invalid/HiddenOverride",
      "verification/invalid/HOInvocations",
      "verification/invalid/i497",
      "verification/invalid/i1295",
      "verification/invalid/InductTacticTest",
      "verification/invalid/InsertionSort",
      "verification/invalid/IntSet",
      "verification/invalid/IntSetUnit",
      "verification/invalid/InvisibleOpaque",
      "verification/invalid/Issue1167",
      "verification/invalid/Issue1167b",
      "verification/invalid/LawsExampleInvalid",
      "verification/invalid/ListOperations",
      "verification/invalid/Lists",
      "verification/invalid/Nested15",
      "verification/invalid/PackedFloat8",
      "verification/invalid/PartialSplit",
      "verification/invalid/PositiveMap",
      "verification/invalid/PositiveMap2",
      "verification/invalid/PropositionalLogic",
      "verification/invalid/RedBlackTree",
      "verification/invalid/RedBlackTree2",
      "verification/invalid/SimpleQuantification2",
      "verification/invalid/SpecWithExtern",

      // false-valid/ (for greater good...)
      "verification/false-valid/ForestNothing2",
    )

  private val ignoreCodegen = Set(
    // Does not work with --feeling-lucky. See #490
    "verification/valid/MsgQueue",
    // assertion failed in `compileLambda`
    "verification/valid/GodelNumbering"
  )

  override protected def optionsString(options: inox.Options): String = {
    "solvr=" + options.findOptionOrDefault(inox.optSelectedSolvers).head + " " +
    "lucky=" + options.findOptionOrDefault(inox.solvers.unrolling.optFeelingLucky) + " " +
    "check=" + options.findOptionOrDefault(inox.solvers.optCheckModels) + " " +
    "codegen=" + options.findOptionOrDefault(evaluators.optCodeGen)
  }

  override def configurations: Seq[Seq[inox.OptionValue[?]]] = {
    // All configurations for all possible solvers and codegen / recursive evaluators
    // Note 1: For codegen, we only use Z3
    // Note 2: We opt-in for early counter-example discovery for codegen with the "feeling lucky" option
    for {
      solver <- solvers
      codeGen <- Seq(false, true)
      if !codeGen || solver == "smt-z3"
      conf <- super.configurations.map {
        seq =>
          Seq(
            inox.optSelectedSolvers(Set(solver)),
            inox.solvers.optCheckModels(true),
            evaluators.optCodeGen(codeGen),
            inox.solvers.unrolling.optFeelingLucky(codeGen)) ++ seq
      }
    } yield conf
  }

  override def filter(ctx: inox.Context, name: String): FilterStatus = {
    val solvers = ctx.options.findOptionOrDefault(inox.optSelectedSolvers)
    assert(solvers.size == 1)
    val ignoredSolver = solvers.head match {
      case "smt-z3" => ignoreZ3(name)
      case "smt-cvc4" | "smt-cvc5" => ignoreCVC(name)
      case "princess" => ignorePrincess(name)
      case other => fail(s"An unknown solver: $other")
    }
    val ignoredCodegen = ctx.options.findOptionOrDefault(evaluators.optCodeGen) && ignoreCodegen(name)
    if (ignoredSolver || ignoredCodegen) Ignore else super.filter(ctx, name)
  }

  import VerificationSuite._

  testPosAll("verification/valid", valid._1, valid._2)

  testNegAll("verification/invalid", invalid._1, invalid._2)

  // Tests that should be rejected, but aren't
  testPosAll("verification/false-valid", falseValid._1, falseValid._2)
}
object VerificationSuite {
  private lazy val valid = ComponentTestSuite.loadPrograms("verification/valid", recursive = true)
  private lazy val invalid = ComponentTestSuite.loadPrograms("verification/invalid")
  private lazy val falseValid = ComponentTestSuite.loadPrograms("verification/false-valid")
}
