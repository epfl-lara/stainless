/* Copyright 2009-2018 EPFL, Lausanne */

package stainless
package wasmgen
package wasm

import scala.language.implicitConversions
import Types._

// A subset of instructions defined by the WASM standard
object Expressions { self =>

  abstract class Sign
  case object Signed   extends Sign { override def toString = "s" }
  case object Unsigned extends Sign { override def toString = "u" }

  trait RelOp
  trait SignedOp {
    val sign: Sign
    private val name = getClass.getSimpleName

    override def toString = s"${name}_$sign"
  }

  abstract class UnOp {
    def apply(e1: Expr) = Unary(this, e1)
  }
  // Int only
  case object eqz extends UnOp with RelOp // Return 1 if operand is 0, 0 otherwise
  // TODO: Add the rest
  // Float only
  case object neg extends UnOp with RelOp
  // TODO: ADD the rest



  abstract class BinOp {
    def apply(e1: Expr, e2: Expr) = Binary(this, e1, e2)
  }

  // mk: This is a little hacky since we use the same names for multiple operations but oh well
  // Int and float instructions
  case object add extends BinOp
  case object sub extends BinOp
  case object mul extends BinOp
  case object eq  extends BinOp with RelOp
  case object ne  extends BinOp with RelOp
  // Int only
  case class div(sign: Sign) extends BinOp with SignedOp
  case class rem(sign: Sign) extends BinOp with SignedOp
  case object and extends BinOp
  case object or  extends BinOp
  case object xor extends BinOp
  case object shl extends BinOp
  case class shr(sign: Sign) extends BinOp with SignedOp
  case object rotl extends BinOp
  case object rotr extends BinOp
  case class lt(sign: Sign) extends BinOp with SignedOp with RelOp
  case class le(sign: Sign) extends BinOp with SignedOp with RelOp
  case class gt(sign: Sign) extends BinOp with SignedOp with RelOp
  case class ge(sign: Sign) extends BinOp with SignedOp with RelOp
  // float only
  case object div extends BinOp
  case object min extends BinOp
  case object max extends BinOp
  case object copysign extends BinOp
  case object lt extends BinOp with RelOp
  case object le extends BinOp with RelOp
  case object gt extends BinOp with RelOp
  case object ge extends BinOp with RelOp

  abstract class Expr { val getType: Type }

  // Operators
  case class Binary(op: BinOp, lhs: Expr, rhs: Expr) extends Expr {
    val getType = op match {
      case _: RelOp => i32
      case _ => lhs.getType
    }
  }
  case class Unary(op: UnOp, expr: Expr) extends Expr {
    val getType = op match {
      case _: RelOp => i32
      case _ => expr.getType
    }
  }

  // Conversions
  case class Extend(to: Type, sign: Sign, e: Expr) extends Expr {
    val getType = to
  }
  case class Wrap(to: Type, e: Expr) extends Expr {
    val getType = to
  }
  case class Truncate(to: Type, sign: Sign, e: Expr) extends Expr {
    val getType = to
  }

  // Constants
  trait Const extends Expr
  case class I32Const(value: Int)    extends Expr with Const { val getType = i32 }
  case class I64Const(value: Long)   extends Expr with Const { val getType = i64 }
  case class F32Const(value: Float)  extends Expr with Const { val getType = f32 }
  case class F64Const(value: Double) extends Expr with Const { val getType = f64 }

  // Control instructions
  case class If(label: Label, cond: Expr, thenn: Expr, elze: Expr) extends Expr {
    val getType = thenn.getType
  }
  // A block of instructions with a label at the beginning
  case class Loop(label: Label, body: Expr) extends Expr {
    val getType = body.getType
  }
  // A block of instructions with a label at the end
  case class Block(label: Label, body: Expr) extends Expr {
    val getType = body.getType
  }
  // Jump to "label", which MUST be the label of an enclosing structure
  case class Br(label: Label) extends Expr {
    val getType = void
  }

  case class BrIf(label: Label, cond: Expr) extends Expr {
    val getType = void
  }

  case class BrTable(labels: Seq[Label], default: Label, index: Expr, body: Option[Expr]) extends Expr {
    val getType = body.map(_.getType).getOrElse(void)
  }

  case class Call(name: Label, tpe: Type, args: Seq[Expr]) extends Expr {
    val getType = tpe
  }

  case class CallIndirect(tpe: Type, func: Expr, args: Seq[Expr]) extends Expr {
    val getType = tpe
  }

  case class Return(value: Expr) extends Expr {
    val getType = void
  }
  case class Drop(value: Expr) extends Expr {
    val getType = void
  }
  case object Unreachable extends Expr {
    val getType = void
  }
  case object Nop extends Expr {
    val getType = void
  }

  case class Load(tpe: Type, truncate: Option[(TruncType,Sign)], address: Expr) extends Expr {
    val getType = tpe
  }

  case class Store(truncate: Option[TruncType], address: Expr, value: Expr) extends Expr {
    val getType = void
  }

  case object MemorySize extends Expr {
    val getType = i32
  }

  case class MemoryGrow(size: Expr) extends Expr {
    val getType: Type = i32
  }

  // Variable instructions
  case class GetLocal(label: Label)(implicit lh: LocalsHandler) extends Expr {
    val getType = lh.getType(label)
  }
  case class SetLocal(l: Label, value: Expr) extends Expr {
    val getType = void
  }

  case class GetGlobal(label: Label)(implicit gh: GlobalsHandler) extends Expr {
    val getType = gh.getType(label)
  }
  case class SetGlobal(l: Label, value: Expr) extends Expr {
    val getType = void
  }

  // A sequence of instructions, 0 or 1 of which is allowed to leave a value on the stack
  case class Sequence(es: Seq[Expr]) extends Expr {
    val getType = es.map(_.getType).filter(_ != void) match {
      case Seq() => void
      case Seq(tpe) => tpe
      case other => sys.error(s"Sequence $es contains multiple values with non-void types")
    }
  }

  // Helpers
  def zero(tpe: Type): Const = tpe match {
    case `i32` => I32Const(0)
    case `i64` => I64Const(0)
    case `f32` => F32Const(0)
    case `f64` => F64Const(0)
  }

}
