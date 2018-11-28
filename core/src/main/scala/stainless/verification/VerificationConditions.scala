/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package verification

import inox.solvers.Solver

/** This is just to hold some history information. */
case class VC[T <: ast.Trees](condition: T#Expr, fd: Identifier, kind: VCKind, satisfiability: Boolean)
  extends inox.utils.Positioned

sealed abstract class VCKind(val name: String, val abbrv: String) {
  override def toString = name
  def underlying = this
}

object VCKind {
  case class Info(k: VCKind, info: String) extends VCKind(k.abbrv+" ("+info+")", k.abbrv) {
    override def underlying = k.underlying
  }

  case object Precondition                  extends VCKind("precondition", "precond.")
  case object Postcondition                 extends VCKind("postcondition", "postcond.")
  case object Assert                        extends VCKind("body assertion", "assert.")
  case object ExhaustiveMatch               extends VCKind("match exhaustiveness", "match.")
  case object ArrayUsage                    extends VCKind("array usage", "arr. use")
  case object MapUsage                      extends VCKind("map usage", "map use")
  case object Overflow                      extends VCKind("integer overflow", "overflow")
  case object Shift                         extends VCKind("strict arithmetic on shift", "shift")
  case object DivisionByZero                extends VCKind("division by zero", "div 0")
  case object ModuloByZero                  extends VCKind("modulo by zero", "mod 0")
  case object MeasureDecreases              extends VCKind("measure decreases", "measure")
  case object MeasurePositive               extends VCKind("non-negative measure", "measure")
  case object UnfoldType                    extends VCKind("strictly positive index for ADT selection", "unfold")
  case object RemainderByZero               extends VCKind("remainder by zero", "rem 0")
  case object CastError                     extends VCKind("cast correctness", "cast")
  case object PostTactic                    extends VCKind("postcondition tactic", "tact.")
  case object Choose                        extends VCKind("choose satisfiability", "choose")
  case object Law                           extends VCKind("law", "law")
  case object InvariantSat                  extends VCKind("invariant satisfiability", "inv. sat")
  case class  AssertErr(err: String)        extends VCKind("body assertion: " + err, "assert.")
  case class  Error(err: String)            extends VCKind(err, "error")
  case class  AdtInvariant(inv: Identifier) extends VCKind("adt invariant", "adt inv.")

  def fromErr(optErr: Option[String]) = {
    optErr.map { err =>
      if (err.startsWith("Array ")) VCKind.ArrayUsage
      else if (err.startsWith("Map ")) VCKind.MapUsage
      else if (err.endsWith("Overflow")) VCKind.Overflow
      else if (err.startsWith("Shift")) VCKind.Shift
      else if (err.startsWith("Division ")) VCKind.DivisionByZero
      else if (err.startsWith("Modulo ")) VCKind.ModuloByZero
      else if (err.startsWith("Remainder ")) VCKind.RemainderByZero
      else if (err.startsWith("Cast ")) VCKind.CastError
      else VCKind.AssertErr(err)
    }.getOrElse(VCKind.Assert)
  }
}

sealed abstract class VCStatus[+Model](val name: String) {
  override def toString = name
}

object VCStatus {
  sealed abstract class Reason[+Model]
  case class CounterExample[+Model](model: Model) extends Reason[Model]
  case object Unsatisfiable extends Reason[Nothing]

  case class Invalid[+Model](reason: Reason[Model]) extends VCStatus[Model]("invalid")
  case object Valid extends VCStatus[Nothing]("valid")
  case object ValidFromCache extends VCStatus[Nothing]("valid from cache")
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
  def isValid           = status == VCStatus.Valid || isValidFromCache
  def isValidFromCache  = status == VCStatus.ValidFromCache
  def isInvalid         = status.isInstanceOf[VCStatus.Invalid[_]]
  def isInconclusive    = !isValid && !isInvalid
}

