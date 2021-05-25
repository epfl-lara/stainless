/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package phases

import ir.IRs.{ RIR, SIR }
import ir.StructInliner

trait StructInliningPhase extends LeonPipeline[RIR.Prog, SIR.Prog] {
  val name = "StructInlining"

  private implicit val debugSection = DebugSectionGenC

  def run(sprog: RIR.Prog): SIR.Prog = new StructInliner(context)(sprog)
}

object StructInliningPhase {
  def apply(implicit ctx: inox.Context): LeonPipeline[RIR.Prog, SIR.Prog] = new {
    val context = ctx
  } with StructInliningPhase
}
