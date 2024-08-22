/* Copyright 2009-2021 EPFL, Lausanne */

package stainless
package genc
package ir

import PrimitiveTypes._

/*
 * Collection of operators for IR with their precedence from the Scala language perspective.
 */
private[genc] object Operators {

  // NOTE It is possible to have more than one "From" or several "To", but this is not expected!
  //      (It will compile but ungracefully do not what is expected...)
  //
  // NOTE It is also expected that ToIntegral is combined with FromIntegral.
  //
  // NOTE The subset of operators supported here has luckily the same precedence
  //      rules in Scala/Java and C. We base the numbering here on the C one:
  //      http://en.cppreference.com/w/c/language/operator_precedence#Literals
  sealed trait Operator { this: From & To =>
    val symbol: String
    val precedence: Int

    override def toString = symbol
  }

  sealed trait From
  trait FromIntegral extends From
  trait FromLogical extends From
  trait FromPairOfT extends From // twice the same argument type, includes both FromIntegral and FromLogical

  sealed trait To
  trait ToIntegral extends To
  trait ToLogical extends To

  trait Integral extends FromIntegral with ToIntegral
  trait Logical extends FromLogical with ToLogical
  trait Ordered extends FromIntegral with ToLogical

  abstract class UnaryOperator(val symbol: String, val precedence: Int) extends Operator { this: From & To => }
  abstract class BinaryOperator(val symbol: String, val precedence: Int) extends Operator { this: From & To => }

  case object Plus extends BinaryOperator("+", 4) with Integral
  case object UMinus extends UnaryOperator("-", 2) with Integral
  case object Minus extends BinaryOperator("-", 4) with Integral
  case object Times extends BinaryOperator("*", 3) with Integral
  case object Div extends BinaryOperator("/", 3) with Integral
  case object Modulo extends BinaryOperator("%", 3) with Integral

  case object LessThan extends BinaryOperator("<", 6) with Ordered
  case object LessEquals extends BinaryOperator("<=", 6) with Ordered
  case object GreaterEquals extends BinaryOperator(">=", 6) with Ordered
  case object GreaterThan extends BinaryOperator(">", 6) with Ordered
  case object Equals extends BinaryOperator("==", 7) with FromPairOfT with ToLogical
  case object NotEquals extends BinaryOperator("!=", 7) with FromPairOfT with ToLogical

  case object Not extends UnaryOperator("!", 2) with Logical
  case object And extends BinaryOperator("&&", 11) with Logical
  case object Or extends BinaryOperator("||", 12) with Logical

  case object BNot extends UnaryOperator("~", 2) with Integral
  case object BAnd extends BinaryOperator("&", 8) with Integral // NOTE to avoid warning from compilers,
  case object BXor extends BinaryOperator("^", 8) with Integral //      we make sure to add parenthesis
  case object BOr extends BinaryOperator("|", 8) with Integral  //      for those three operators...
  // ... even though it's safe no to add parenthesis.

  case object BLeftShift extends BinaryOperator("<<", 5) with Integral
  case object BRightShift extends BinaryOperator(">>", 5) with Integral

}
