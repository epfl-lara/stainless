/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package solvers

import inox.solvers._
import inox.solvers.combinators._

import evaluators._

object SolverFactory {

  def getFromName(name: String)
                 (p: Program, opts: inox.Options)
                 (enc: inox.ast.ProgramTransformer {
                    val sourceProgram: p.type
                    val targetProgram: StainlessProgram
                  })(implicit sem: p.Semantics): SolverFactory { val program: p.type; type S <: TimeoutSolver { val program: p.type } } = {
    if (inox.solvers.SolverFactory.solvers(name)) {
      val checkedOpt = optAssumeChecked(PurityOptions.AssumeChecked)
      inox.solvers.SolverFactory.getFromName(name)(p, opts + checkedOpt)(enc andThen InoxEncoder(enc.targetProgram))
    } else {
      sys.error("TODO!")
    }
  }

  // Note that in case of a portfolio solver, we will share the evaluator and encoder
  // between all underlying solvers. We count on immutability to ensure sanity here.
  def getFromNames(names: Seq[String])
                  (p: Program, opts: inox.Options)
                  (enc: inox.ast.ProgramTransformer {
                     val sourceProgram: p.type
                     val targetProgram: StainlessProgram
                   })(implicit sem: p.Semantics): SolverFactory { val program: p.type; type S <: TimeoutSolver { val program: p.type } } = {
    names match {
      case Seq() => throw new inox.FatalError("No selected solver")
      case Seq(single) => getFromName(single)(p, opts)(enc)
      case multiple => PortfolioSolverFactory(p) {
        multiple.map(name => getFromName(name)(p, opts)(enc))
      }
    }
  }

  def getFromSettings(p: Program, opts: inox.Options)
                     (enc: inox.ast.ProgramTransformer {
                        val sourceProgram: p.type
                        val targetProgram: StainlessProgram
                      })(implicit sem: p.Semantics): SolverFactory { val program: p.type; type S <: TimeoutSolver { val program: p.type } } = {
    val names = opts.findOptionOrDefault(inox.optSelectedSolvers).toSeq
    getFromNames(names)(p, opts)(enc)
  }

  def apply(name: String, p: StainlessProgram, opts: inox.Options): SolverFactory {
    val program: p.type
    type S <: TimeoutSolver { val program: p.type }
  } = getFromName(name)(p, opts)(inox.ast.ProgramEncoder.empty(p))(p.getSemantics)

  def apply(p: StainlessProgram, opts: inox.Options): SolverFactory {
    val program: p.type
    type S <: TimeoutSolver { val program: p.type }
  } = getFromSettings(p, opts)(inox.ast.ProgramEncoder.empty(p))(p.getSemantics)

  def default(p: StainlessProgram): SolverFactory {
    val program: p.type
    type S <: TimeoutSolver { val program: p.type }
  } = apply(p, p.ctx.options)
}
