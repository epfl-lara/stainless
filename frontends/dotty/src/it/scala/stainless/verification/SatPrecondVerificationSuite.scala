/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import scala.concurrent.duration._

import org.scalatest._

/** Checks the satisfiability of preconditions with the given mode of `--sat-precond`, on the
 *  benchmarks of `directory`. */
abstract class AbstractSatPrecondVerificationSuite(mode: SatPrecondMode, directory: String) extends VerificationComponentTestSuite {
  private val solvers = Seq("smt-z3", "smt-cvc5", "princess")

  private val ignoreCommon: Set[String] = Set()

  private val ignoreZ3: Set[String] = ignoreCommon ++
    Set()

  private val ignoreCVC: Set[String] = ignoreCommon ++
    Set()

  private val ignorePrincess: Set[String] = ignoreCommon ++
    Set("sat-precondition/valid/SATPrecond4") ++
    Set("sat-precondition/valid/SATPrecond5")

  private val ignoreCodegen: Set[String] = Set()

  override protected def optionsString(options: inox.Options): String = {
    "solvr=" + options.findOptionOrDefault(inox.optSelectedSolvers).head + " " +
    "lucky=" + options.findOptionOrDefault(inox.solvers.unrolling.optFeelingLucky) + " " +
    "check=" + options.findOptionOrDefault(inox.solvers.optCheckModels) + " " +
    "codegen=" + options.findOptionOrDefault(evaluators.optCodeGen) + " " +
    "sat-precond=" + options.findOptionOrDefault(stainless.optSatPrecond)
  }

  override def configurations: Seq[Seq[inox.OptionValue[?]]] = {
    // All configurations for all possible solvers and codegen / recursive evaluators
    // Note 1: For codegen, we only use Z3
    // Note 2: We opt-in for early counter-example discovery for codegen with the "feeling lucky" option
    for {
      solver <- solvers
      codeGen <- Seq(false)
      if !codeGen || solver == "smt-z3"
      conf <- super.configurations.map {
        seq =>
          Seq(
            stainless.optSatPrecond(mode),
            inox.optSelectedSolvers(Set(solver)),
            inox.solvers.optCheckModels(true),
            evaluators.optCodeGen(codeGen),
            inox.optTimeout(3.seconds),
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

  private lazy val valid = ComponentTestSuite.loadPrograms(s"$directory/valid", recursive = true)
  private lazy val invalid = ComponentTestSuite.loadPrograms(s"$directory/invalid")

  testPosAll(s"$directory/valid", valid)

  testNegAll(s"$directory/invalid", invalid)
}

/** `--sat-precond=all`: the preconditions of all functions */
class SatPrecondVerificationSuite extends AbstractSatPrecondVerificationSuite(SatPrecondMode.All, "sat-precondition")

/** `--sat-precond=annotated`: only the preconditions of the functions annotated with
 *  @checkSatPrecondition */
class SatPrecondAnnotatedVerificationSuite extends AbstractSatPrecondVerificationSuite(SatPrecondMode.Annotated, "sat-precondition-annotated")

/** The witnesses of the satisfiability of preconditions, given by `precondWitness`. They are checked
 *  whatever the mode of `--sat-precond`; with `annotated`, they replace the satisfiability check of
 *  the preconditions of the annotated functions. */
class PrecondWitnessVerificationSuite extends AbstractSatPrecondVerificationSuite(SatPrecondMode.Annotated, "precond-witness")
