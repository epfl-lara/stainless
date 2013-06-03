/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package verification

import solvers.Solver

import java.util.concurrent.atomic.AtomicBoolean

case class VerificationContext (
  context: LeonContext,
  solvers: Seq[Solver],
  reporter: Reporter,
  shouldStop: AtomicBoolean = new AtomicBoolean(false)
)
