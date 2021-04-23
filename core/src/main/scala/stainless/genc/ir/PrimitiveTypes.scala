/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package ir

/*
 * Collection of the primitive types for IR.
 */
private[genc] object PrimitiveTypes {

  sealed abstract class PrimitiveType {
    def isLogical: Boolean = this match {
      case BoolType => true
      case _ => false
    }

    def isIntegral: Boolean = this match {
      case _: IntegralPrimitiveType => true
      case _ => false
    }
  }

  sealed abstract class IntegralPrimitiveType extends PrimitiveType {
    def isSigned: Boolean =
      this == Int8Type ||
      this == Int16Type ||
      this == Int32Type ||
      this == Int64Type

    def isUnsigned: Boolean =
      this == UInt8Type ||
      this == UInt16Type ||
      this == UInt32Type ||
      this == UInt64Type

    def toUnsigned: IntegralPrimitiveType = this match {
      case Int8Type => UInt8Type
      case Int16Type => UInt16Type
      case Int32Type => UInt32Type
      case Int64Type => UInt64Type
      case _ => sys.error(s"cannot invoke toUnsigned on $this")
    }
  }

  case object CharType extends IntegralPrimitiveType
  case object Int8Type extends IntegralPrimitiveType
  case object Int16Type extends IntegralPrimitiveType
  case object Int32Type extends IntegralPrimitiveType
  case object Int64Type extends IntegralPrimitiveType
  case object UInt8Type extends IntegralPrimitiveType
  case object UInt16Type extends IntegralPrimitiveType
  case object UInt32Type extends IntegralPrimitiveType
  case object UInt64Type extends IntegralPrimitiveType
  case object BoolType extends PrimitiveType
  case object UnitType extends PrimitiveType
  case object StringType extends PrimitiveType

}
