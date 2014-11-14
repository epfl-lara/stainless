/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package verification

import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._

abstract class Tactic(vctx: VerificationContext) {
  val description : String
  val shortDescription : String

  val program  = vctx.program
  val reporter = vctx.reporter

  def generateVCs(fdUnsafe: FunDef): Seq[VerificationCondition] = {
    val fd = fdUnsafe.duplicate
    fd.fullBody = matchToIfThenElse(fd.fullBody)
    generatePostconditions(fd) ++
    generatePreconditions(fd) ++
    generateCorrectnessConditions(fd)
  }

  def generatePostconditions(function: FunDef): Seq[VerificationCondition]
  def generatePreconditions(function: FunDef): Seq[VerificationCondition]
  def generateCorrectnessConditions(function: FunDef): Seq[VerificationCondition]


  // Helper functions
  protected def precOrTrue(fd: FunDef): Expr = fd.precondition match {
    case Some(pre) => pre
    case None => BooleanLiteral(true)
  }

  protected def collectWithPC[T](f: PartialFunction[Expr, T])(expr: Expr): Seq[(T, Expr)] = {
    CollectorWithPaths(f).traverse(expr)
  }
}
