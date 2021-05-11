/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package phases

import ir.IRs.{ LIR, RIR }
import ir.{ Referentiator }

/*
 * This phase identify which variable should be reference instead of value,
 * and make sure reference are dereferenced before being accessed.
 *
 * Add ReferenceType, Ref and Deref to the input CIR program.
 *
 * NOTE a ReferenceType(T) is basically a T* in C.
 */
private[genc] object ReferencingPhase extends LeonPipeline[LIR.Prog, RIR.Prog] {
  val name = "Referencer"
  val description = "Add 'referencing' to the input LIR program to produce a RIR program"

  private implicit val debugSection = DebugSectionGenC

  def getTimer(ctx: inox.Context) = ctx.timers.genc.get("CIR -> RIR")

  def run(ctx: inox.Context, lprog: LIR.Prog): RIR.Prog = {
    new Referentiator(ctx)(lprog)
  }
}
