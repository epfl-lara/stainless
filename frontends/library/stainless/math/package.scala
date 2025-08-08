/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import stainless.annotation.*
import stainless.lang.*

import scala.language.implicitConversions

package object math {

  /** Disable overflow checks within `body`.
    *
    * This is equivalent to setting `--strict-arithmetic=false` for `body` only.
    */
  @ignore
  def wrapping[A](body: A): A = body

  @library
  def min(i1: Int, i2: Int) = if (i1 <= i2) i1 else i2

  @library
  def max(i1: Int, i2: Int) = if (i1 >= i2) i1 else i2

  @library
  def min(i1: Long, i2: Long) = if (i1 <= i2) i1 else i2

  @library
  def max(i1: Long, i2: Long) = if (i1 >= i2) i1 else i2

  @library
  def min(x: Float, y: Float): Float = scala.math.min(x, y)

  @library
  def max(x: Float, y: Float): Float = scala.math.max(x, y)

  @library
  def min(x: Double, y: Double): Double = scala.math.min(x, y)

  @library
  def max(x: Double, y: Double): Double = scala.math.max(x, y)

  @library
  def min(i1: BigInt, i2: BigInt) = if (i1 <= i2) i1 else i2

  @library
  def max(i1: BigInt, i2: BigInt) = if (i1 >= i2) i1 else i2

  @library
  def max(i1: BigInt, i2: BigInt, i3: BigInt) = if (i1 >= i2) i1 else if (i2 >= i3) i2 else i3

  @library
  def min(i1: Nat, i2: Nat) = if (i1 <= i2) i1 else i2

  @library
  def max(i1: Nat, i2: Nat) = if (i1 >= i2) i1 else i2

  @library
  def abs(n: BigInt) = if(n < 0) -n else n

  @library
  def abs(x: Float) = scala.math.abs(x)

  @library
  def abs(x: Double) = scala.math.abs(x)

  @library
  def floor(x: Double) = scala.math.floor(x)

  @library
  def ceil(x: Double) = scala.math.ceil(x)

  @library
  def rint(x: Double) = scala.math.rint(x)

  val E: Double = 2.7182818284590452354

  val Pi: Double = 3.14159265358979323846

  @library
  implicit def bigIntToNat(b: BigInt): Nat = {
    require(b >= 0)
    Nat(b)
  }

  @ignore
  def sqrt(a: Double): Double = {
    java.lang.Math.sqrt(a)
  }

  // Properties based on rules in the KeY verifier are ensured below. //

  @extern @pure @library
  def sin(x: Double): Double = {
    java.lang.Math.sin(x)
  }.ensuring(res =>
    ((x.isNaN || x.isInfinity) == res.isNaN)
    && ((x.isPositive && x.isZero) ==> (res.isPositive && res.isZero))
    && ((x.isNegative && x.isZero) ==> (res.isNegative && res.isZero))
    && (-1.0d <= res && res <= 1.0d || res.isNaN)
  )

  @extern @pure @library
  def cos(x: Double): Double = {
    java.lang.Math.cos(x)
  }.ensuring(res =>
    ((x.isNaN || x.isInfinity) == res.isNaN)
    && (-1.0d <= res && res <= 1.0d || res.isNaN)
  )

  @extern @pure @library
  def asin(x: Double): Double = {
    java.lang.Math.asin(x)
  }.ensuring(res =>
    ((x.isNaN || x < -1.0d || x > 1.0d) ==> res.isNaN)
    && ((x.isPositive && x.isZero) ==> (res.isPositive && res.isZero))
    && ((x.isNegative && x.isZero) ==> (res.isNegative && res.isZero))
    && ((-1.0d <= x && x <= 1.0d) ==> (-1.5707963267948966d <= res && res <= 1.5707963267948966d))
  )

  @extern @pure @library
  def acos(x: Double): Double = {
    java.lang.Math.acos(x)
  }.ensuring(res =>
    ((x.isNaN || x < -1.0d || x > 1.0d) ==> res.isNaN)
    && ((!x.isNaN && -1.0d <= x && x <= 1.0d) ==> (0.0d <= res && res <= 3.14159265358979323846d))
  )

  @extern @pure @library
  def tan(x: Double): Double = {
    java.lang.Math.tan(x)
  }.ensuring(res =>
    ((x.isNaN || x.isInfinity) ==> res.isNaN)
    && ((x.isPositive && x.isZero) ==> (res.isPositive && res.isZero))
    && ((x.isNegative && x.isZero) ==> (res.isNegative && res.isZero))
  )

  @extern @pure @library
  def log(x: Double): Double = {
    scala.math.log(x)
  }.ensuring( res =>
    if x.isNaN || x < 0 then res.isNaN
    else if x.isZero then res.isNegInfinity
    else if x == 1.0 then res.isZero && res.isPositive
    else !res.isNaN
  )

  @extern @pure @library
  def atan2(y: Double, x: Double): Double = {
    java.lang.Math.atan2(y, x)
  }.ensuring(res =>
    ((y.isNaN || x.isNaN) == res.isNaN)
    && (y.isNaN || x.isNaN || -3.14159265358979323846d <= res && res <= 3.14159265358979323846d)
  )

  @extern @pure @library
  def pow(a: Double, b: Double) = {
    java.lang.Math.pow(a, b)
  }.ensuring(res =>
    (b.isZero ==> (res == 1.0))
    && ((!a.isNaN && b == 1.0) ==> (res == a))
    && (b.isNaN ==> res.isNaN)
    && ((a.isNaN && !b.isZero) ==> res.isNaN)
    && (((a < -1.0d || a > 1.0d) && b.isPositive && b.isInfinity) ==> (res.isPositive && res.isInfinity))
    && ((-1.0d < a && a < 1.0d && b.isNegative && b.isInfinity) ==> (res.isPositive && res.isInfinity))
    && (((a < -1.0d || a > 1.0d) && b.isNegative && b.isInfinity) ==> (res.isPositive && res.isZero))
    && ((-1.0d < a && a < 1.0d && b.isPositive && b.isInfinity) ==> (res.isPositive && res.isZero))
    && (((a == 1.0d || a == -1.0d) && b.isInfinity) ==> res.isNaN)
    && ((a.isPositive && a.isZero && b > 0) ==> (res.isPositive && res.isZero))
    && ((a.isPositive && a.isInfinity && b < 0) ==> (res.isPositive && res.isZero))
    && ((a.isPositive && a.isZero && b < 0) ==> (res.isPositive && res.isInfinity))
    && ((a.isPositive && a.isInfinity && b > 0) ==> (res.isPositive && res.isInfinity))
    && ((a.isPositive && b.isFinite) ==> res.isPositive)
    && ((!a.isNaN && b == 2) ==> res.isPositive)
  )

  @extern @pure @library
  def exp(a: Double): Double = {
    java.lang.Math.exp(a)
  }.ensuring(res =>
    (a.isNaN == res.isNaN)
    && ((a.isPositive && a.isInfinity) ==> (res.isPositive && res.isInfinity))
    && ((a.isNegative && a.isInfinity) ==> (res.isPositive && res.isZero))
    && (!a.isNaN ==> res.isPositive)
  )

  @extern @pure @library
  def log1p(x: Double): Double = {
    scala.math.log1p(x)
  }.ensuring(res =>
    ((x.isNaN || x < -1) == res.isNaN)
    && (x.isPosInfinity ==> res.isPosInfinity)
    && (x == -1 ==> res.isNegInfinity)
    && (x.isZero ==> (res == x))
    && (x.isPositive ==> res.isPositive)
  )

  @extern @pure @library
  def atan(x: Double): Double = {
    java.lang.Math.atan(x)
  }.ensuring(res =>
    (x.isNaN ==> res.isNaN)
    && ((x.isPositive && x.isZero) ==> (res.isPositive && res.isZero))
    && ((x.isNegative && x.isZero) ==> (res.isNegative && res.isZero))
    && (-1.5707963267948966d <= res && res <= 1.5707963267948966d || x.isNaN)
  )

  @extern @pure @library
  def hypot(x: Double, y: Double): Double = {
    scala.math.hypot(x, y)
  }.ensuring(res =>
    ((x.isInfinity || y.isInfinity) ==> res.isPosInfinity)
    && (((x.isNaN && y.isFinite) || (x.isNaN && y.isNaN) || (x.isFinite && y.isNaN)) == res.isNaN)
    && ((x.isFinite && y.isFinite) ==> res.isPositive)
  )
}

