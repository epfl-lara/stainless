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
class ReferencingPhase(using override val context: inox.Context) extends LeonPipeline[LIR.Prog, RIR.Prog](context) {
  val name = "Referencer"

  private given givenDebugSection: DebugSectionGenC.type = DebugSectionGenC

  def run(lprog: LIR.Prog): RIR.Prog = new Referentiator(context)(lprog)
}
