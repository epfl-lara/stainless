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
      case Int32Lit(_) => Int32Type
      case BoolLit(_) => BoolType
      case UnitLit => UnitType
      case StringLit(_) => StringType
    }

    override def toString: String = this match {
      case CharLit(v) => "'" + escape(v) + "'"
      case Int8Lit(v) => s"$v"
      case Int32Lit(v) => s"$v"
      case BoolLit(v) => s"$v"
      case UnitLit => s"()"
      case StringLit(v) => '"' + escape(v) + '"'
    }
  }

  case class CharLit(v: Char) extends Literal

  case class Int8Lit(v: Byte) extends Literal

  case class Int32Lit(v: Int) extends Literal

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
