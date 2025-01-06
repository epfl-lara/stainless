/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package verification

import inox.solvers.Solver

/** This is just to hold some history information. */
case class VC[T <: ast.Trees](val trees: T)(val condition: trees.Expr, val fid: Identifier, val kind: VCKind, val satisfiability: Boolean)
  extends inox.utils.Positioned {

  // We override hashCode and equals because, for some reasons, the synthesized methods only use `trees` and ignore the rest

  override def canEqual(that: Any): Boolean = that.isInstanceOf[VC[?]]

  override def equals(other: Any): Boolean = other match {
    case that: VC[t] =>
      trees == that.trees &&
        condition == that.condition &&
        fid == that.fid &&
        kind == that.kind &&
        satisfiability == that.satisfiability
    case _ => false
  }

  override def hashCode(): Int = {
    val state = Seq(trees, condition, fid, kind, satisfiability)
    state.map(_.hashCode()).foldLeft(0)((a, b) => 31 * a + b)
  }

  override def toString(): String =  s"VC($condition)"
}

sealed abstract class VCKind(val name: String, val abbrv: String) {
  override def toString = name
  def underlying = this

  def isMeasureRelated: Boolean = this match {
    case VCKind.MeasureDecreases | VCKind.MeasurePositive | VCKind.MeasureMissing => true
    case _ => false
  }
}

object VCKind {
  case class Info(k: VCKind, info: String) extends VCKind(k.abbrv+" ("+info+")", k.abbrv) {
    override def underlying = k.underlying
  }

  case object CheckType                     extends VCKind("type-checking", "types")
  case object Precondition                  extends VCKind("precondition", "precond.")
  case object Postcondition                 extends VCKind("postcondition", "postcond.")
  case object Assert                        extends VCKind("body assertion", "assert.")
  case object ExhaustiveMatch               extends VCKind("match exhaustiveness", "match.")
  case object ArrayUsage                    extends VCKind("array index within bounds", "arr. bounds")
  case object MapUsage                      extends VCKind("map index in keys", "map use")
  case object Overflow                      extends VCKind("integer overflow", "overflow")
  case object Shift                         extends VCKind("strict arithmetic on shift", "shift")
  case object DivisionByZero                extends VCKind("division by zero", "div 0")
  case object ModuloByZero                  extends VCKind("modulo by zero", "mod 0")
  case object MeasureDecreases              extends VCKind("measure decreases", "measure")
  case object MeasurePositive               extends VCKind("non-negative measure", "measure")
  case object MeasureMissing                extends VCKind("measure missing", "measure")
  case object UnfoldType                    extends VCKind("strictly positive index for ADT selection", "unfold")
  case object RemainderByZero               extends VCKind("remainder by zero", "rem 0")
  case object CastError                     extends VCKind("cast correctness", "cast")
  case object PostTactic                    extends VCKind("postcondition tactic", "tact.")
  case object Choose                        extends VCKind("choose satisfiability", "choose")
  case object Law                           extends VCKind("law", "law")
  case object InvariantSat                  extends VCKind("invariant satisfiability", "inv. sat")
  case object RefinementSubtype             extends VCKind("refinements checks for subtyping", "refinements")
  case object RecursiveSubtype              extends VCKind("recursive types indices checks for subtyping", "rec. types")
  case class  AssertErr(err: String)        extends VCKind("body assertion: " + err, "assert.")
  case object CoqMethod                     extends VCKind("coq function", "coq fun.")
  case class  Error(err: String)            extends VCKind(err, "error")
  case class  AdtInvariant(inv: Identifier) extends VCKind("class invariant", "class inv.")
  case object SATPrecondCheck               extends VCKind("precondition satisfiability", "sat precond.")

  def fromErr(optErr: Option[String]) = {
    optErr.map { err =>
      if (err.startsWith("Array ")) VCKind.ArrayUsage
      else if (err.startsWith("Map ")) VCKind.MapUsage
      else if (err.endsWith("Overflow")) VCKind.Overflow
      else if (err.startsWith("Shift")) VCKind.Shift
      else if (err.startsWith("Division by zero")) VCKind.DivisionByZero
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
  case object Admitted extends VCStatus[Nothing]("admitted")
  case object ValidFromCache extends VCStatus[Nothing]("valid from cache")
  case object Trivial extends VCStatus[Nothing]("trivial")
  case object Unknown extends VCStatus[Nothing]("unknown")
  case object Timeout extends VCStatus[Nothing]("timeout")
  case object Cancelled extends VCStatus[Nothing]("cancelled")
  case object Crashed extends VCStatus[Nothing]("crashed")
  case object Unsupported extends VCStatus[Nothing]("unsupported")
  case object ExternalBug extends VCStatus[Nothing]("external bug")
}

case class VCResult[+Model](
  status: VCStatus[Model],
  solverName: Option[String],
  time: Option[Long],
  smtLibFileId: Option[Int]
) {
  def isValid           = status == VCStatus.Valid || isValidFromCache || isTrivial
  def isValidFromCache  = status == VCStatus.ValidFromCache
  def isTrivial         = status == VCStatus.Trivial
  def isAdmitted        = status == VCStatus.Admitted
  def isInvalid         = status.isInstanceOf[VCStatus.Invalid[?]]
  def isInconclusive    = !isValid && !isInvalid
}
