/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package phases

import ir.IRs.{ NIR, LIR }
import ir.{ ClassLifter }

/*
 * This phase lifts class types to their top level class and add appropriate
 * AsA cast to make sure the output program works on the same inputs.
 *
 * This is done in order to use tagged union to represent classes in C.
 */
class LiftingPhase(using override val context: inox.Context) extends LeonPipeline[NIR.Prog, LIR.Prog](context) {
  val name = "Lifter"

  private given givenDebugSection: DebugSectionGenC.type = DebugSectionGenC

  def run(nprog: NIR.Prog): LIR.Prog = new ClassLifter(context)(nprog)
}
