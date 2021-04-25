/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package phases

import ir.IRs.{ CIR, NIR }
import ir.{ Normaliser }

/*
 * Normalise the program by adding explicit execution points and making sure
 * argument-like expressions are "simple" expressions (and not e.g. blocks).
 */
private[genc] object NormalisationPhase extends LeonPipeline[CIR.Prog, NIR.Prog] {
  val name = "Normaliser"
  val description = "Normalise IR to match the C execution model"

  private implicit val debugSection = DebugSectionGenC

  def getTimer(ctx: inox.Context) = ctx.timers.genc.get("CIR -> NIR")

  def run(ctx: inox.Context, cprog: CIR.Prog): NIR.Prog = {

    val normaliser = new Normaliser(ctx)
    val nprog = normaliser(cprog)

    ctx.reporter.debug("RESUTING NIR PROGRAM:\n" + nprog)

    nprog
  }
}
