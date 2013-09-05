/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package verification

import solvers._

import java.util.concurrent.atomic.AtomicBoolean

case class VerificationContext (
  context: LeonContext,
  solvers: Seq[SolverFactory[Solver]],
  reporter: Reporter
)
