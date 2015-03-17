/* Copyright 2009-2014 EPFL, Lausanne */

package leon.verification

import leon.purescala.Expressions._
import leon.purescala.Definitions._
import leon.purescala.Common._
import leon.utils.{Position, Positioned}

import leon.solvers._

/** This is just to hold some history information. */
class VerificationCondition(val condition: Expr, val funDef: FunDef, val kind: VCKind, val tactic: Tactic, val info: String = "") extends Positioned {
  // None = still unknown
  // Some(true) = valid
  // Some(false) = invalid
  var hasValue = false
  var value : Option[Boolean] = None
  var solvedWith : Option[Solver] = None
  var time : Option[Double] = None
  var counterExample : Option[Map[Identifier, Expr]] = None

  def status : String = value match {
    case None => "unknown"
    case Some(true) => "valid"
    case Some(false) => "invalid"
  }

  def tacticStr = tactic.shortDescription match {
    case "default" => ""
    case s => s
  }

  def solverStr = solvedWith match {
    case Some(s) => s.name
    case None => ""
  }

  override def toString = {
    kind.toString + " in function " + funDef.id.name + "\n" +
    condition.toString
  }

}

abstract class VCKind(val name: String, val abbrv: String) {
  override def toString = name
}
case object VCPrecondition    extends VCKind("precondition", "precond.")
case object VCPostcondition   extends VCKind("postcondition", "postcond.")
case object VCAssert          extends VCKind("body assertion", "assert.")
case object VCExhaustiveMatch extends VCKind("match exhaustiveness", "match.")
case object VCMapUsage        extends VCKind("map usage", "map use")
case object VCArrayUsage      extends VCKind("array usage", "arr. use")
