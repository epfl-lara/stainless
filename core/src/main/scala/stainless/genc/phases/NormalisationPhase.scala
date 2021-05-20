/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package phases

import ir.IRs.{ CIR, NIR }
import ir.Normaliser

/*
 * Normalise the program by adding explicit execution points and making sure
 * argument-like expressions are "simple" expressions (and not e.g. blocks).
 */
trait NormalisationPhase extends LeonPipeline[CIR.Prog, NIR.Prog] {
  val name = "Normaliser"

  private implicit val debugSection = DebugSectionGenC

  def run(cprog: CIR.Prog): NIR.Prog = new Normaliser(context)(cprog)
}

object NormalisationPhase {
  def apply(implicit ctx: inox.Context): LeonPipeline[CIR.Prog, NIR.Prog] = new {
    val context = ctx
  } with NormalisationPhase
}
