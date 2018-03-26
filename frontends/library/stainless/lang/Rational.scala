/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.lang

import stainless.annotation._

import scala.language.implicitConversions

@library
case class Rational(numerator: BigInt, denominator: BigInt) {

  require(this.isRational)

  def +(that: Rational): Rational = {
    Rational(this.numerator*that.denominator + that.numerator*this.denominator, this.denominator*that.denominator)
  }

  def -(that: Rational): Rational = {
    Rational(this.numerator*that.denominator - that.numerator*this.denominator, this.denominator*that.denominator)
  }

  def unary_- : Rational = {
    Rational(-this.numerator, this.denominator)
  }

  def *(that: Rational): Rational = {
    Rational(this.numerator*that.numerator, this.denominator*that.denominator)
  }

  def /(that: Rational): Rational = {
    require(that.nonZero)
    val newNumerator = this.numerator*that.denominator
    val newDenominator = this.denominator*that.numerator
    normalize(newNumerator, newDenominator)
  }

  def reciprocal: Rational = {
    require(this.nonZero)
    normalize(this.denominator, this.numerator)
  }


  def ~(that: Rational): Boolean = {
    this.numerator*that.denominator == that.numerator*this.denominator
  }

  def <(that: Rational): Boolean = {
    this.numerator*that.denominator < that.numerator*this.denominator
  }

  def <=(that: Rational): Boolean = {
    this.numerator*that.denominator <= that.numerator*this.denominator
  }

  def >(that: Rational): Boolean = {
    this.numerator*that.denominator > that.numerator*this.denominator
  }

  def >=(that: Rational): Boolean = {
    this.numerator*that.denominator >= that.numerator*this.denominator
  }

  def nonZero: Boolean = {
    numerator != 0
  }

  private def isRational: Boolean = denominator > 0

  private def normalize(num: BigInt, den: BigInt): Rational = {
    require(den != 0)
    if(den < 0)
      Rational(-num, -den)
    else
      Rational(num, den)
  }
}

@library
object Rational {

  implicit def bigIntToRat(n: BigInt): Rational = Rational(n, 1)

  def apply(n: BigInt): Rational = Rational(n, 1)

}
