/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

import inox.solvers.Solver

/** This is just to hold some history information. */
case class VC[T <: ast.Trees](condition: T#Expr, fd: Identifier, kind: VCKind) extends inox.utils.Positioned

/*
case class VC(condition: Expr, fd: FunDef, kind: VCKind) extends Positioned {
  override def toString = {
    fd.id.name +" - " +kind.toString
  }
  // If the two functions are the same but have different positions, used to transfer one to the other.
  def copyTo(newFun: FunDef) = {
    val thisPos = this.getPos
    val newPos = ExprOps.lookup(_.getPos == thisPos, _.getPos)(fd.fullBody, newFun.fullBody) match {
      case Some(position) => position
      case None => newFun.getPos
    }
    val newCondition = ExprOps.lookup(condition == _, i => i)(fd.fullBody, newFun.fullBody).getOrElse(condition)
    VC(newCondition, newFun, kind).setPos(newPos)
  }
}
*/

sealed abstract class VCKind(val name: String, val abbrv: String) {
  override def toString = name
  def underlying = this
}

object VCKind {
  case class Info(k: VCKind, info: String) extends VCKind(k.abbrv+" ("+info+")", k.abbrv) {
    override def underlying = k
  }

  case object Precondition    extends VCKind("precondition", "precond.")
  case object Postcondition   extends VCKind("postcondition", "postcond.")
  case object Assert          extends VCKind("body assertion", "assert.")
  case object ExhaustiveMatch extends VCKind("match exhaustiveness", "match.")
  case object ArrayUsage      extends VCKind("array usage", "arr. use")
  case object MapUsage        extends VCKind("map usage", "map use")
  case object DivisionByZero  extends VCKind("division by zero", "div 0")
  case object ModuloByZero    extends VCKind("modulo by zero", "mod 0")
  case object RemainderByZero extends VCKind("remainder by zero", "rem 0")
  case object CastError       extends VCKind("cast correctness", "cast")
  case object PostTactVC      extends VCKind("Postcondition Tactic", "tact")
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
}

case class VCResult[T <: ast.Trees](
  status: VCStatus[Map[T#ValDef, T#Expr]],
  solver: Option[Solver],
  time: Option[Long]
) {
  def isValid   = status == VCStatus.Valid
  def isInvalid = status.isInstanceOf[VCStatus.Invalid[_]]
  def isInconclusive = !isValid && !isInvalid
}

