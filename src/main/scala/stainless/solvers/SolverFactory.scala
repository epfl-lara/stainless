/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package solvers

object SolverFactory {
  
  def getFromName(name: String)
                 (p: StainlessProgram, opts: inox.Options)
                 (ev: DeterministicEvaluator with SolvingEvaluator { val program: p.type }):
                  SolverFactory { val program: p.type; type S <: TimeoutSolver } = {
    if (inox.solvers.SolverFactory.solvers(name)) {
      val sf = inox.solvers.SolverFactory.getFromName(name)
      new {
        val program: p.type = p

      }
    } else {
      sys.error("TODO!")
    }
  }
}
