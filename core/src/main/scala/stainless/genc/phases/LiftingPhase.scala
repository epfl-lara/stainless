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
private[genc] object LiftingPhase extends LeonPipeline[NIR.Prog, LIR.Prog] {
  val name = "Lifter"
  val description = "Lift class types to their hierarchy top class"

  private implicit val debugSection = DebugSectionGenC

  def getTimer(ctx: inox.Context) = ctx.timers.genc.get("NIR -> LIR")

  def run(ctx: inox.Context, nprog: NIR.Prog): LIR.Prog = {

    val lifter = new ClassLifter(ctx)
    val lprog = lifter(nprog)

    ctx.reporter.debug("RESUTING LIR PROGRAM:\n" + lprog.toString())

    lprog
  }
}
