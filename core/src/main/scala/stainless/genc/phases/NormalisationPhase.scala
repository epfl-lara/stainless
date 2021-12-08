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
class NormalisationPhase(using override val context: inox.Context) extends LeonPipeline[CIR.Prog, NIR.Prog](context) {
  val name = "Normaliser"

  private given givenDebugSection: DebugSectionGenC.type = DebugSectionGenC

  def run(cprog: CIR.Prog): NIR.Prog = new Normaliser(context)(cprog)
}
