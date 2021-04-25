/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package ir

import PrimitiveTypes._

/*
 * Collection of literal genres for IR.
 */
private[genc] object Literals {

  sealed abstract class Literal {
    def getPrimitiveType: PrimitiveType = this match {
      case CharLit(_) => CharType
      case Int8Lit(_) => Int8Type
      case Int16Lit(_) => Int16Type
      case Int32Lit(_) => Int32Type
      case Int64Lit(_) => Int64Type
      case UInt8Lit(_) => UInt8Type
      case UInt16Lit(_) => UInt16Type
      case UInt32Lit(_) => UInt32Type
      case UInt64Lit(_) => UInt64Type
      case BoolLit(_) => BoolType
      case UnitLit => UnitType
      case StringLit(_) => StringType
    }

    override def toString: String = this match {
      case CharLit(v) => "'" + escape(v) + "'"
      case Int8Lit(v) => s"$v"
      case Int16Lit(v) => s"$v"
      case Int32Lit(v) => s"$v"
      case Int64Lit(v) => s"$v"
      case UInt8Lit(v) => s"$v"
      case UInt16Lit(v) => s"$v"
      case UInt32Lit(v) => s"$v"
      case UInt64Lit(v) => s"$v"
      case BoolLit(v) => s"$v"
      case UnitLit => s"()"
      case StringLit(v) => '"' + escape(v) + '"'
    }
  }

  case class CharLit(v: Char) extends Literal

  case class Int8Lit(v: BigInt) extends Literal
  case class Int16Lit(v: BigInt) extends Literal
  case class Int32Lit(v: BigInt) extends Literal
  case class Int64Lit(v: BigInt) extends Literal

  case class UInt8Lit(v: BigInt) extends Literal
  case class UInt16Lit(v: BigInt) extends Literal
  case class UInt32Lit(v: BigInt) extends Literal
  case class UInt64Lit(v: BigInt) extends Literal

  case class BoolLit(v: Boolean) extends Literal

  case object UnitLit extends Literal

  case class StringLit(v: String) extends Literal

  /** Some little helper to properly print char/string literals **/
  private def escape(c: Char): String = c match {
    case '\b' => "\\b"
    case '\t' => "\\t"
    case '\n' => "\\n"
    case '\f' => "\\f"
    case '\r' => "\\r"
    case '\\' => "\\\\"
    case '\'' => "\\'"
    case '\"' => "\\\""
    case c    => c.toString
  }

  private def escape(s: String): String = {
    import org.apache.commons.lang3.StringEscapeUtils
    StringEscapeUtils.escapeJava(s)
  }

}
