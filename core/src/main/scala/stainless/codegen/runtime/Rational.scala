/* Copyright 2009-2019 EPFL, Lausanne */

package stainless.codegen.runtime

import java.math.BigInteger

object Rational {
  def isZero(bi: BigInteger): Boolean = bi.signum == 0
  def isLEZ(bi: BigInteger): Boolean = bi.signum != 1
  def isLTZ(bi: BigInteger): Boolean = bi.signum == -1
  def isGEZ(bi: BigInteger): Boolean = bi.signum != -1
  def isGTZ(bi: BigInteger): Boolean = bi.signum == 1
}

final class Rational(_num: BigInteger, _denom: BigInteger) {
  import Rational._

  private val (num, denom) = {
    val divisor = _num.abs.gcd(_denom.abs)
    val simpNum = _num.divide(divisor)
    val simpDenom = _denom.divide(divisor)

    if (isLTZ(simpDenom)) {
      (simpNum.negate, simpDenom.negate)
    } else {
      (simpNum, simpDenom)
    }
  }

  def this(num: String, denom: String) = this(new BigInteger(num), new BigInteger(denom))

  def numerator: BigInteger = num
  def denominator: BigInteger = denom

  def add(that: Rational): Rational = new Rational(
    num.multiply(that.denom).add(that.num.multiply(denom)),
    denom.multiply(that.denom)
  )

  def sub(that: Rational): Rational = new Rational(
    num.multiply(that.denom).subtract(that.num.multiply(denom)),
    denom.multiply(that.denom)
  )

  def mult(that: Rational): Rational = new Rational(
    num.multiply(that.num),
    denom.multiply(that.denom)
  )

  def div(that: Rational): Rational = new Rational(
    num.multiply(that.denom),
    denom.multiply(that.num)
  )

  def neg: Rational = new Rational(num.negate, denom)

  def lessThan(that: Rational): Boolean = isLTZ(this.sub(that).num)
  def lessEquals(that: Rational): Boolean = isLEZ(this.sub(that).num)
  def greaterThan(that: Rational): Boolean = isGTZ(this.sub(that).num)
  def greaterEquals(that: Rational): Boolean = isGEZ(this.sub(that).num)

  override def equals(that: Any): Boolean = that match {
    case r: Rational => isZero(this.sub(r).num)
    case _ => false
  }

  override def hashCode: Int = num.hashCode ^ denom.hashCode

  override def toString: String = num.toString + "/" + denom.toString
}
