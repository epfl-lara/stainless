/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package phases

import ir.IRs.{ RIR, SIR }
import ir.StructInliner

class StructInliningPhase(using override val context: inox.Context) extends LeonPipeline[RIR.Prog, SIR.Prog](context) {
  val name = "StructInlining"

  private given givenDebugSection: DebugSectionGenC.type = DebugSectionGenC

  def run(sprog: RIR.Prog): SIR.Prog = new StructInliner(context)(sprog)
}
