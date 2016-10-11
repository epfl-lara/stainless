/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package solvers

import inox.solvers._
import inox.solvers.combinators._
import inox.evaluators.{DeterministicEvaluator, SolvingEvaluator}

import evaluators._

object SolverFactory {

  def getFromName(name: String)
                 (p: inox.Program, opts: inox.Options)
                 (ev: DeterministicEvaluator with SolvingEvaluator { val program: p.type },
                   enc: ProgramEncoder { val sourceProgram: p.type; val t: inox.trees.type }):
                  SolverFactory { val program: p.type; type S <: TimeoutSolver } = {
    if (inox.solvers.SolverFactory.solvers(name)) {
      inox.solvers.SolverFactory.getFromName(name)(p, opts)(ev, enc)
    } else {
      sys.error("TODO!")
    }
  }

  def apply(name: String, p: StainlessProgram, opts: inox.Options): SolverFactory {
    val program: p.type
    type S <: TimeoutSolver
  } = getFromName(name)(p, opts)(RecursiveEvaluator(p, opts), InoxEncoder(p))

  def apply(p: StainlessProgram, opts: inox.Options): SolverFactory  {
    val program: p.type
    type S <: TimeoutSolver
  } = opts.findOptionOrDefault(inox.InoxOptions.optSelectedSolvers).toSeq match {
    case Seq() => throw new inox.FatalError("No selected solver")
    case Seq(single) => apply(single, p, opts)
    case multiple => PortfolioSolverFactory(p) {
      multiple.map(name => apply(name, p, opts))
    }
  }

  def default(p: StainlessProgram): SolverFactory { val program: p.type; type S <: TimeoutSolver } =
    apply(p, p.ctx.options)
}
