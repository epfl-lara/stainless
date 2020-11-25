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

  sealed abstract class IntegralPrimitiveType extends PrimitiveType

  case object CharType extends IntegralPrimitiveType
  case object Int8Type extends IntegralPrimitiveType
  case object UInt32Type extends IntegralPrimitiveType
  case object Int32Type extends IntegralPrimitiveType
  case object BoolType extends PrimitiveType
  case object UnitType extends PrimitiveType
  case object StringType extends PrimitiveType

}
