/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package verification

import purescala.Definitions.Program
import solvers._

import java.util.concurrent.atomic.AtomicBoolean

case class VerificationContext (
  context: LeonContext,
  program: Program,
  solvers: Seq[SolverFactory[Solver]],
  reporter: Reporter
)
