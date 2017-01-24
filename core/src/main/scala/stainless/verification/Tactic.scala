/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

trait Tactic {
  val program: Program
  val description: String

  protected type VC = verification.VC[program.trees.type]
  protected def VC(cond: program.trees.Expr, id: Identifier, kind: VCKind): VC = verification.VC(cond, id, kind)

  def generateVCs(id: Identifier): Seq[VC] = {
    generatePostconditions(id) ++
    generatePreconditions(id) ++
    generateCorrectnessConditions(id)
  }

  def generatePostconditions(id: Identifier): Seq[VC]
  def generatePreconditions(id: Identifier): Seq[VC]
  def generateCorrectnessConditions(id: Identifier): Seq[VC]

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
