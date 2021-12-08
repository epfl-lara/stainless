/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import scala.collection.mutable.ListBuffer

trait Tactic {
  val program: Program
  val context: inox.Context
  val description: String

  import program.trees._
  import program.symbols.{given, _}

  protected type VC = verification.VC[program.trees.type]
  protected def VC(cond: program.trees.Expr, id: Identifier, kind: VCKind, satisfiability: Boolean): VC =
    verification.VC(program.trees)(cond, id, kind, satisfiability)

  protected def collectForConditions[T](pf: PartialFunction[(Expr, Path),T])(e: Expr): Seq[T] = {
    val results: ListBuffer[T] = new ListBuffer
    val lifted = pf.lift

    transformWithPC(e, true /* recurse into types */)((e, path, op) => e match {
      case Annotated(_, flags) if flags contains DropVCs => e
      case _ =>
        lifted(e, path).foreach(results += _)
        op.sup(e, path)
    })

    results.toList
  }

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
