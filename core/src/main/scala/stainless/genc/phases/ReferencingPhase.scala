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
trait ReferencingPhase extends LeonPipeline[LIR.Prog, RIR.Prog] {
  val name = "Referencer"

  private implicit val debugSection = DebugSectionGenC

  def run(lprog: LIR.Prog): RIR.Prog = new Referentiator(context)(lprog)
}

object ReferencingPhase {
  def apply(implicit ctx: inox.Context): LeonPipeline[LIR.Prog, RIR.Prog] = new {
    val context = ctx
  } with ReferencingPhase
}
