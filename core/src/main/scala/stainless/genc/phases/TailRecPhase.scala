package stainless
package genc
package phases

import ir.IRs.{ SIR, TIR }
import ir.TailRecTransformer

class TailRecPhase(using override val context: inox.Context) extends LeonPipeline[SIR.Prog, TIR.Prog](context) {
  val name = "TailRec"

  private given givenDebugSection: DebugSectionGenC.type = DebugSectionGenC

  def run(sprog: SIR.Prog): TIR.Prog = new TailRecTransformer(context)(sprog)
}

