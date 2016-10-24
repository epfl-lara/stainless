/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package verification

import purescala.Definitions.Program
import solvers._

class VerificationContext(
  context: LeonContext,
  val program: Program,
  val solverFactory: SolverFactory[Solver]
) extends LeonContext(
  context.reporter,
  context.interruptManager,
  context.options,
  context.files,
  context.classDir,
  context.timers
) {
  lazy val checkInParallel: Boolean = context.findOptionOrDefault(VerificationPhase.optParallelVCs)
}
