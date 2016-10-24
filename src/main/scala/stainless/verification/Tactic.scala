/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package verification

import purescala.Definitions._
import purescala.Expressions._

abstract class Tactic(vctx: VerificationContext) {
  val description : String

  implicit val ctx = vctx

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
