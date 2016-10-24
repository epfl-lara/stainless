/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

trait Tactic {
  val program: Program
  val description: String

  def generateVCs(id: Identifier): Seq[VC { val trees: program.trees.type }] = {
    generatePostconditions(id) ++
    generatePreconditions(id) ++
    generateCorrectnessConditions(id)
  }

  def generatePostconditions(id: Identifier): Seq[VC { val trees: program.trees.type }]
  def generatePreconditions(id: Identifier): Seq[VC { val trees: program.trees.type }]
  def generateCorrectnessConditions(id: Identifier): Seq[VC { val trees: program.trees.type }]

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
