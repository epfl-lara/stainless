package stainless
package genc
package phases

import ir.IRs.{ SIR, TIR }
import ir.TailRecTransformer
import ir.TailRecSimpTransformer

class TailRecPhase(using override val context: inox.Context) extends LeonPipeline[SIR.Prog, TIR.Prog](context) {
  val name = "TailRec"

  private given givenDebugSection: DebugSectionGenC.type = DebugSectionGenC

  def run(sprog: SIR.Prog): TIR.Prog =
    val simplTransformer = new TailRecSimpTransformer
    val sprog1 = simplTransformer(sprog)
    new TailRecTransformer(context)(sprog1)
}

