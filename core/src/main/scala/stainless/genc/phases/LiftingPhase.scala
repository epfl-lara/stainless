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
trait LiftingPhase extends LeonPipeline[NIR.Prog, LIR.Prog] {
  val name = "Lifter"

  private implicit val debugSection = DebugSectionGenC

  def run(nprog: NIR.Prog): LIR.Prog = new ClassLifter(context)(nprog)
}

object LiftingPhase {
  def apply(implicit ctx: inox.Context): LeonPipeline[NIR.Prog, LIR.Prog] = new {
    val context = ctx
  } with LiftingPhase
}
