/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package verification

import purescala.Definitions._
import purescala.Expressions._

/**
 * This tactic applies only to non-recursive functions.
 * Inducts over the recursive calls of the first recursive procedure, in the body of `funDef`
 */
class TraceInductionTactic(vctx: VerificationContext) extends Tactic(vctx) {
  val description : String =

  implicit protected val ctx = vctx.context

  def generateVCs(fd: FunDef): Seq[VC] = {
    generatePostconditions(fd) ++
    generatePreconditions(fd) ++
    generateCorrectnessConditions(fd)
  }

  def generatePostconditions(function: FunDef): Seq[VC]
  def generatePreconditions(function: FunDef): Seq[VC]
  def generateCorrectnessConditions(function: FunDef): Seq[VC]

  protected def sizeLimit(s: String, limit: Int) = {
    require(limit > 3)
    // Crop the call to display it properly
    val res = s.takeWhile(_ != '\n').take(limit)
    if (res == s) {
      res
    } else {
      res + " ..."
    }
  }
}
