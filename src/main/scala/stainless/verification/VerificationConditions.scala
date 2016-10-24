/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package verification

/** This is just to hold some history information. */
trait VC extends inox.utils.Positioned {
  val trees: ast.Trees
  val condition: trees.Expr
  val fd: Identifier
  val kind: VCKind
}

object VC {
  def apply(p: Program)(cond: p.trees.Expr, fid: Identifier, vckind: VCKind) = new VC {
    val trees: p.trees.type = p.trees
    val condition = cond
    val fd = fid
    val kind = vckind
  }
}

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

trait VCResult {
  val program: Program
  import program._
  import program.trees._
  import program.symbols.{asString => _, _}

  val status: VCStatus[Map[ValDef, Expr]]
  val solver: Option[inox.solvers.Solver]
  val time: Option[Long]

  def isValid   = status == VCStatus.Valid
  def isInvalid = status.isInstanceOf[VCStatus.Invalid[_]]
  def isInconclusive = !isValid && !isInvalid

  def report(): Unit = status match {
    case VCStatus.Valid =>
      ctx.reporter.info(" => VALID")

    case VCStatus.Invalid(cex) =>
      ctx.reporter.warning(" => INVALID")
      ctx.reporter.warning("Found counter-example:")

      val strings = cex.toSeq.sortBy(_._1.id.name).map {
        case (id, v) => (asString(id), v.asString)
      }

      if (strings.nonEmpty) {
        val max = strings.map(_._1.length).max

        for ((id, v) <- strings) {
          ctx.reporter.warning(("  %-"+max+"s -> %s").format(id, v))
        }
      } else {
        ctx.reporter.warning(f"  (Empty counter-example)")
      }

    case _ =>
      ctx.reporter.warning(" => " + status.name.toUpperCase)
  }
}

object VCResult {
  def apply(p: Program)
           (res: VCStatus[Map[p.trees.ValDef, p.trees.Expr]], s: Option[inox.solvers.Solver], t: Option[Long]):
            VCResult { val program: p.type } = {
    new VCResult {
      val program: p.type = p
      val status = res
      val solver = s
      val time = t
    }
  }
}
