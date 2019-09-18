/* Copyright 2009-2019 EPFL, Lausanne */

package stainless.codegen.runtime

import java.math.BigInteger

object BigInt {
  lazy val ZERO = new BigInt(BigInteger.ZERO)
  lazy val ONE  = new BigInt(BigInteger.ONE)
}

final class BigInt private(private val underlying: BigInteger) {
  def this(value: String) = this(new BigInteger(value))
  def this(value: Int) = this(new BigInteger(value.toString))

  def toScala: scala.BigInt = scala.BigInt(underlying)
  def toInt: Int = underlying.intValue

  def add(that: BigInt): BigInt = new BigInt(underlying.add(that.underlying))
  def sub(that: BigInt): BigInt = new BigInt(underlying.subtract(that.underlying))
  def mult(that: BigInt): BigInt = new BigInt(underlying.multiply(that.underlying))
  def div(that: BigInt): BigInt = new BigInt(underlying.divide(that.underlying))
  def rem(that: BigInt): BigInt = new BigInt(underlying.remainder(that.underlying))
  def mod(that: BigInt): BigInt =
    new BigInt(if (that.underlying.compareTo(BigInteger.ZERO) < 0) {
      underlying.mod(that.underlying.negate)
    } else {
      underlying.mod(that.underlying)
    })

  def neg: BigInt = new BigInt(underlying.negate)

  def lessThan(that: BigInt): Boolean = underlying.compareTo(that.underlying) < 0
  def lessEquals(that: BigInt): Boolean = underlying.compareTo(that.underlying) <= 0
  def greaterThan(that: BigInt): Boolean = underlying.compareTo(that.underlying) > 0
  def greaterEquals(that: BigInt): Boolean = underlying.compareTo(that.underlying) >= 0

  override def equals(that: Any): Boolean = that match {
    case b: BigInt => underlying.equals(b.underlying)
    case _ => false
  }

  override def hashCode: Int = underlying.hashCode

  override def toString: String = underlying.toString
}
