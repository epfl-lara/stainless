/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package solvers

import inox.solvers._
import inox.solvers.combinators._
import inox.evaluators.{DeterministicEvaluator, SolvingEvaluator}

import evaluators._

object SolverFactory {

  def getFromName(name: String)
                 (p: Program, opts: inox.Options)
                 (ev: DeterministicEvaluator with SolvingEvaluator { val program: p.type },
                   enc: inox.ast.ProgramEncoder { val sourceProgram: p.type; val t: inox.trees.type }):
                  SolverFactory { val program: p.type; type S <: TimeoutSolver { val program: p.type } } = {
    if (inox.solvers.SolverFactory.solvers(name)) {
      inox.solvers.SolverFactory.getFromName(name)(p, opts)(ev, enc)
    } else {
      sys.error("TODO!")
    }
  }

  // Note that in case of a portfolio solver, we will share the evaluator and encoder
  // between all underlying solvers. We count on immutability to ensure sanity here.
  def getFromNames(names: Seq[String])
                  (p: Program, opts: inox.Options)
                  (ev: DeterministicEvaluator with SolvingEvaluator { val program: p.type },
                    enc: inox.ast.ProgramEncoder { val sourceProgram: p.type; val t: inox.trees.type }):
                   SolverFactory { val program: p.type; type S <: TimeoutSolver { val program: p.type } } = {
    names match {
      case Seq() => throw new inox.FatalError("No selected solver")
      case Seq(single) => getFromName(single)(p, opts)(ev, enc)
      case multiple => PortfolioSolverFactory(p) {
        multiple.map(name => getFromName(name)(p, opts)(ev, enc))
      }
    }
  }

  def getFromSettings(p: Program, opts: inox.Options)
                     (ev: DeterministicEvaluator with SolvingEvaluator { val program: p.type },
                       enc: inox.ast.ProgramEncoder { val sourceProgram: p.type; val t: inox.trees.type }):
                      SolverFactory { val program: p.type; type S <: TimeoutSolver { val program: p.type } } = {
    val names = opts.findOptionOrDefault(inox.InoxOptions.optSelectedSolvers).toSeq
    getFromNames(names)(p, opts)(ev, enc)
  }

  def apply(name: String, p: StainlessProgram, opts: inox.Options): SolverFactory {
    val program: p.type
    type S <: TimeoutSolver { val program: p.type }
  } = getFromName(name)(p, opts)(Evaluator(p, opts), InoxEncoder(p))

  def apply(p: StainlessProgram, opts: inox.Options): SolverFactory {
    val program: p.type
    type S <: TimeoutSolver { val program: p.type }
  } = getFromSettings(p, opts)(Evaluator(p, opts), InoxEncoder(p))

  def default(p: StainlessProgram): SolverFactory {
    val program: p.type
    type S <: TimeoutSolver { val program: p.type }
  } = apply(p, p.ctx.options)
}
