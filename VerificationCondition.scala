/* Copyright 2009-2015 EPFL, Lausanne */

package leon.verification

import leon.purescala.Expressions._
import leon.purescala.Definitions._
import leon.purescala.Types._
import leon.purescala.PrettyPrinter
import leon.utils.Positioned
import leon.evaluators.StringTracingEvaluator
import leon.solvers._
import leon.LeonContext

/** This is just to hold some history information. */
case class VC(condition: Expr, fd: FunDef, kind: VCKind) extends Positioned {
  override def toString = {
    fd.id.name +" - " +kind.toString
  }
}

abstract class VCKind(val name: String, val abbrv: String) {
  override def toString = name

  def underlying = this
}

object VCKinds {
  case class Info(k: VCKind, info: String) extends VCKind(k.abbrv+" ("+info+")", k.abbrv) {
    override def underlying = k
  }

  case object Precondition    extends VCKind("precondition", "precond.")
  case object Postcondition   extends VCKind("postcondition", "postcond.")
  case object Assert          extends VCKind("body assertion", "assert.")
  case object ExhaustiveMatch extends VCKind("match exhaustiveness", "match.")
  case object MapUsage        extends VCKind("map usage", "map use")
  case object ArrayUsage      extends VCKind("array usage", "arr. use")
  case object DivisionByZero  extends VCKind("division by zero", "div 0")
  case object ModuloByZero    extends VCKind("modulo by zero", "mod 0")
  case object RemainderByZero extends VCKind("remainder by zero", "rem 0")
  case object CastError       extends VCKind("cast correctness", "cast")
}

case class VCResult(status: VCStatus, solvedWith: Option[Solver], timeMs: Option[Long]) {
  def isValid   = status == VCStatus.Valid
  def isInvalid = status.isInstanceOf[VCStatus.Invalid]
  def isInconclusive = !isValid && !isInvalid

  def userDefinedString(v: Expr, orElse: =>String)(vctx: VerificationContext): String = {
    //println(vctx.program.definedFunctions.map(fd => fd.id.name + "," + (fd.returnType == StringType) + ", " + (fd.params.length == 1) + "," + (fd.params.length == 1 && fd.params.head.getType == v.getType)).mkString("\n"))
    (vctx.program.definedFunctions find {
      case fd => fd.returnType == StringType && fd.params.length == 1 && fd.params.head.getType == v.getType && fd.id.name.toLowerCase().endsWith("tostring")
    }) match {
      case Some(fd) =>
        println("Found fd: " + fd.id.name)
        val ste = new StringTracingEvaluator(vctx.context, vctx.program)
        val result = ste.eval(FunctionInvocation(fd.typed, Seq(v)))
        result.result match {
          case Some((StringLiteral(res), _)) =>
            res
          case _ =>
            orElse
        }
      case None =>
        orElse
    }
  }
  
  def report(vctx: VerificationContext) {
    import vctx.reporter
    import vctx.context

    status match {
      case VCStatus.Valid =>
        reporter.info(" => VALID")

      case VCStatus.Invalid(cex) =>
        reporter.warning(" => INVALID")
        reporter.warning("Found counter-example:")

        // We use PrettyPrinter explicitly and not ScalaPrinter: printing very
        // large arrays faithfully in ScalaPrinter is hard, while PrettyPrinter
        // is free to simplify
        val strings = cex.toSeq.sortBy(_._1.name).map {
          case (id, v) =>
            (id.asString(context), userDefinedString(v, PrettyPrinter(v))(vctx))
        }

        if (strings.nonEmpty) {
          val max = strings.map(_._1.length).max

          for ((id, v) <- strings) {
            reporter.warning(("  %-"+max+"s -> %s").format(id, v))
          }
        } else {
          reporter.warning(f"  (Empty counter-example)")
        }
      case _ =>
        reporter.warning(" => "+status.name.toUpperCase)
    }
  }
}

object VCResult {
  def unknown = VCResult(VCStatus.Unknown, None, None)
}

sealed abstract class VCStatus(val name: String) {
  override def toString = name
}

object VCStatus {
  case class  Invalid(cex: Model) extends VCStatus("invalid")
  case object Valid extends VCStatus("valid")
  case object Unknown extends VCStatus("unknown")
  case object Timeout extends VCStatus("timeout")
  case object Cancelled extends VCStatus("cancelled")
}
