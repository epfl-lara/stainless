/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import inox.solvers.Solver

/** This is just to hold some history information. */
case class VC[T <: ast.Trees](condition: T#Expr, fd: Identifier, kind: VCKind) extends inox.utils.Positioned

sealed abstract class VCKind(val name: String, val abbrv: String) {
  override def toString = name
  def underlying = this
}

object VCKind {
  case class Info(k: VCKind, info: String) extends VCKind(k.abbrv+" ("+info+")", k.abbrv) {
    override def underlying = k.underlying
  }

  case object Precondition    extends VCKind("precondition", "precond.")
  case object LambdaPre       extends VCKind("lambda precondition", "lambda pre.")
  case object Postcondition   extends VCKind("postcondition", "postcond.")
  case object Assert          extends VCKind("body assertion", "assert.")
  case object ExhaustiveMatch extends VCKind("match exhaustiveness", "match.")
  case object ArrayUsage      extends VCKind("array usage", "arr. use")
  case object MapUsage        extends VCKind("map usage", "map use")
  case object DivisionByZero  extends VCKind("division by zero", "div 0")
  case object ModuloByZero    extends VCKind("modulo by zero", "mod 0")
  case object RemainderByZero extends VCKind("remainder by zero", "rem 0")
  case object CastError       extends VCKind("cast correctness", "cast")
  case object PostTactic      extends VCKind("postcondition tactic", "tact")
}

sealed abstract class VCStatus[+Model](val name: String) {
  override def toString = name
}

object VCStatus {
  case class Invalid[+Model](cex: Model) extends VCStatus[Model]("invalid")
  case object Valid extends VCStatus[Nothing]("valid")
  case object Unknown extends VCStatus[Nothing]("unknown")
  case object Timeout extends VCStatus[Nothing]("timeout")
  case object Cancelled extends VCStatus[Nothing]("cancelled")
  case object Crashed extends VCStatus[Nothing]("crashed")
  case object Unsupported extends VCStatus[Nothing]("unsupported")
}

case class VCResult[+Model](
  status: VCStatus[Model],
  solver: Option[Solver],
  time: Option[Long]
) {
  def isValid   = status == VCStatus.Valid
  def isInvalid = status.isInstanceOf[VCStatus.Invalid[_]]
  def isInconclusive = !isValid && !isInvalid
}

