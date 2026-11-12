/* Copyright 2009-2026 EPFL, Lausanne */

package stainless
package evaluators

import inox.solvers._

import scala.collection.mutable.{Map => MutableMap}

/** Evaluates the chooses of Stainless, which Inox doesn't have. A choose that the model gives (as
  * the uninterpreted function that encodes it, see [[solvers.InoxEncoder]]) takes its value there,
  * and the others are solved for: their predicates, whose free variables are bound to values, are
  * handed to a solver. Outside of models, the values are cached, so that a choose always has the
  * same value. */
trait ChooseSolving extends inox.evaluators.SolvingEvaluator { self =>
  val program: Program
  import context.{given, _}
  import program._
  import program.trees._
  import program.symbols.{given, _}

  private val chooseCache: MutableMap[Choose, Expr] = MutableMap.empty

  private def hasRefinement(tpe: Type): Boolean =
    typeOps.exists { case _: RefinementType => true case _ => false } (tpe)

  /** A value that satisfies the predicate of `choose`, whose free variables are bound to values,
    * under the interpretations of the model. */
  def onChooseInvocation(choose: Choose, modelInterpretations: Map[(Identifier, Seq[Type]), Expr] = Map.empty): Expr = {
    val Choose(res, pred) = choose
    if (!evalQuantifiers) {
      throw new RuntimeException(s"Evaluation of 'choose' expressions disabled @ ${choose.getPos}")
    }

    // The predicate and the type of the result may call uninterpreted functions
    val interpretations = transitiveInterpretations(Forall(Seq(res), pred), modelInterpretations)

    // The results in a model only hold in that model
    (if (interpretations.isEmpty) chooseCache.get(choose) else None).getOrElse({
      import scala.language.existentials
      import SolverResponses._

      // Solves the predicate. Declaring the result makes the solver respect its type even when the
      // predicate doesn't mention it, as with a result of type `{ v: BigInt | v > 5 }` and predicate `true`,
      // but it also makes the solver look for a value of that type, which may never end: in
      // ForestNothing2, the result's type is an ADT whose invariant only holds for infinite values.
      // So we only declare the result when its type has a refinement and no simple value.
      def solve(declareResult: Boolean): Option[Expr] = {
        val satRes = context.timers.evaluators.specs.run {
          val sf = getSolver(interpretations)(using context)
          val solver = sf.getNewSolver()
          try {
            if (declareResult) solver.declare(res)
            solver.assertCnstr(pred)
            solver.check(Model)
          } finally {
            sf.reclaim(solver)
          }
        }

        satRes match {
          case SatWithModel(model) =>
            if ((model.interpretations.keySet -- interpretations.keySet).nonEmpty && checkModels) {
              throw new RuntimeException("Cannot guarantee model for dependent choose " + choose.asString)
            }
            model.vars.get(res)

          case _ =>
            throw new RuntimeException("Failed to evaluate " + choose.asString)
        }
      }

      val value = solve(declareResult = false).getOrElse {
        try {
          simplestValue(res.tpe, allowSolver = false)
        } catch {
          case _: NoSimpleValue if hasRefinement(res.tpe) => solve(declareResult = true).getOrElse {
            throw new RuntimeException("No simple value for " + choose.asString)
          }
          case _: NoSimpleValue =>
            throw new RuntimeException("No simple value for " + choose.asString)
        }
      }

      if (interpretations.isEmpty) chooseCache(choose) = value
      value
    })
  }
}
