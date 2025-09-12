/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import stainless.annotation.*
import stainless.lang.*

import scala.language.implicitConversions

@library
object FloatConsts {
  /**
   * The number of bits used to represent a float value.
   */
  val SIZE = 32

  /**
   * The number of bits in the significand of a float value.
   */
  val PRECISION = 24

  /**
   * Maximum exponent a finite float variable may have.
   */
  val MAX_EXPONENT: Int = (1 << (SIZE - PRECISION - 1)) - 1 // 127

  /**
   * Minimum exponent a normalized float variable may have.
   */
  val MIN_EXPONENT: Int = 1 - MAX_EXPONENT // -126

  /**
   * The number of logical bits in the significand of a
   * {@code float} number, including the implicit bit.
   */
  val SIGNIFICAND_WIDTH: Int = PRECISION

  /**
   * The exponent the smallest positive {@code float}
   * subnormal value would have if it could be normalized.
   */
  val MIN_SUB_EXPONENT: Int = MIN_EXPONENT - (SIGNIFICAND_WIDTH - 1) // -149


  /**
   * Bias used in representing a {@code float} exponent.
   */
  val EXP_BIAS: Int = (1 << (SIZE - SIGNIFICAND_WIDTH - 1)) - 1 // 127


  /**
   * Bit mask to isolate the sign bit of a {@code float}.
   */
  val SIGN_BIT_MASK: Int = 1 << (SIZE - 1)

  /**
   * Bit mask to isolate the exponent field of a {@code float}.
   */
  val EXP_BIT_MASK: Int = ((1 << (SIZE - SIGNIFICAND_WIDTH)) - 1) << (SIGNIFICAND_WIDTH - 1)

  /**
   * Bit mask to isolate the significand field of a {@code float}.
   */
  val SIGNIF_BIT_MASK: Int = (1 << (SIGNIFICAND_WIDTH - 1)) - 1

  /**
   * Bit mask to isolate the magnitude bits (combined exponent and
   * significand fields) of a {@code float}.
   */
  val MAG_BIT_MASK: Int = EXP_BIT_MASK | SIGNIF_BIT_MASK

}


@library
object DoubleConsts {

  /**
   * A constant holding the smallest positive normal value of type Double
   */
  val MIN_NORMAL = java.lang.Double.longBitsToDouble(0x10000000000000L) // 2.2250738585072014E-308

  /**
   * The number of bits used to represent a {@code double} value.
   */
  val SIZE = 64

  /**
   * The number of bits in the significand of a {@code double} value.
   */
  val PRECISION = 53

  /**
   * Maximum exponent a finite {@code double} variable may have.
   */
  val MAX_EXPONENT: Int = (1 << (SIZE - PRECISION - 1)) - 1 // 1023

  /**
   * Minimum exponent a normalized {@code double} variable may
   * have.
   */
  val MIN_EXPONENT: Int = 1 - MAX_EXPONENT // -1022

  /**
   * The number of logical bits in the significand of a
   * {@code double} number, including the implicit bit.
   */
  val SIGNIFICAND_WIDTH: Int = PRECISION
  /**
   * The exponent the smallest positive {@code double}
   * subnormal value would have if it could be normalized..
   */
  val MIN_SUB_EXPONENT: Int = MIN_EXPONENT - (SIGNIFICAND_WIDTH - 1) // -1074

  /**
   * Bias used in representing a {@code double} exponent.
   */
  val EXP_BIAS: Int = (1 << (SIZE - SIGNIFICAND_WIDTH - 1)) - 1 // 1023

  /**
   * Bit mask to isolate the sign bit of a {@code double}.
   */
  val SIGN_BIT_MASK: Long = 1L << (SIZE - 1)
  /**
   * Bit mask to isolate the exponent field of a {@code double}.
   */
  val EXP_BIT_MASK: Long = ((1L << (SIZE - SIGNIFICAND_WIDTH)) - 1) << (SIGNIFICAND_WIDTH - 1)
  /**
   * Bit mask to isolate the significand field of a {@code double}.
   */
  val SIGNIF_BIT_MASK: Long = (1L << (SIGNIFICAND_WIDTH - 1)) - 1
  /**
   * Bit mask to isolate the magnitude bits (combined exponent and
   * significand fields) of a {@code double}.
   */
  val MAG_BIT_MASK: Long = EXP_BIT_MASK | SIGNIF_BIT_MASK
}

package object math {

  /** The `Double` value that is closer than any other to `e`, the base of
   * the natural logarithms.
   */
  final val E: Double = 2.7182818284590452354

  /** The `Double` value that is closer than any other to `pi`, the ratio of
   * the circumference of a circle to its diameter.
   */
  final val Pi: Double = 3.14159265358979323846

  // MISSING: random()

  @extern @pure @library
  def sin(x: Double): Double = {
    scala.math.sin(x)
  }.ensuring(res =>
    ((x.isNaN || x.isInfinity) == res.isNaN)
      && ((x.isPositive && x.isZero) ==> (res.isPositive && res.isZero))
      && ((x.isNegative && x.isZero) ==> (res.isNegative && res.isZero))
      && (res.isNaN || -1.0d <= res && res <= 1.0d)
  )

  @extern @pure @library
  def cos(x: Double): Double = {
    scala.math.cos(x)
  }.ensuring(res =>
    ((x.isNaN || x.isInfinity) == res.isNaN)
      && (res.isNaN || -1.0d <= res && res <= 1.0d)
  )

  @extern @pure @library
  def tan(x: Double): Double = {
    scala.math.tan(x)
  }.ensuring(res =>
    ((x.isNaN || x.isInfinity) ==> res.isNaN)
      && ((x.isPositive && x.isZero) ==> (res.isPositive && res.isZero))
      && ((x.isNegative && x.isZero) ==> (res.isNegative && res.isZero))
  )

  @library
  def asin(x: Double): Double = {
    FdLibm.Asin.compute(x)
  }.ensuring(res =>
    ((x.isNaN || x < -1.0d || x > 1.0d) == res.isNaN)
      && ((x.isPositive && x.isZero) == (res.isPositive && res.isZero))
      && ((x.isNegative && x.isZero) == (res.isNegative && res.isZero))
      && ((x.isFinite && x == -1.0d) == (res.isFinite && res == -Pi / 2))
      && ((x.isFinite && x == 1.0d) == (res.isFinite && res == Pi / 2))
      && ((x.isFinite && -1.0d <= x && x <= 1.0d) == (res.isFinite && -Pi / 2 <= res && res <= Pi / 2))
  )

  @library
  def acos(x: Double): Double = {
    FdLibm.Acos.compute(x)
  }.ensuring(res =>
    ((x.isNaN || x < -1.0d || x > 1.0d) == res.isNaN)
      && ((x.isFinite && x == 1.0d) ==> (res.isPositive && res.isZero))
      && ((x.isFinite && x == -1.0d) == (res.isFinite && res == stainless.math.Pi))
      && (x.isZero ==> (res == stainless.math.Pi / 2))
      && ((x.isFinite && -1.0d <= x && x <= 1.0d) == (res.isFinite && res.isPositive && 0 <= res && res <= stainless.math.Pi))
  )

  @library
  def atan(x: Double): Double = {
    FdLibm.Atan.compute(x)
  }.ensuring( res =>
    (x.isNaN == res.isNaN)
      && (x.isPositive == res.isPositive)
      && (x.isNegative == res.isNegative)
      && (x.isZero == res.isZero)
      && (!x.isNaN ==> (- Pi / 2 <= res && res <= Pi / 2))
      && (x.isPosInfinity ==> (res == Pi / 2))
      && (x.isNegInfinity ==> (res == -Pi / 2))
  )

  /** Converts an angle measured in degrees to an approximately equivalent
   * angle measured in radians.
   *
   * @param x an angle, in degrees
   * @return the measurement of the angle `x` in radians.
   */
  @library
  def toRadians(x: Double): Double = x.toRadians

  /** Converts an angle measured in radians to an approximately equivalent
   * angle measured in degrees.
   *
   * @param x angle, in radians
   * @return the measurement of the angle `x` in degrees.
   * @group angle-conversion
   */
  @library
  def toDegrees(x: Double): Double = x.toDegrees

  /** Converts rectangular coordinates `(x, y)` to polar `(r, theta)`.
   *
   * @param x the ordinate coordinate
   * @param y the abscissa coordinate
   * @return the ''theta'' component of the point `(r, theta)` in polar
   *         coordinates that corresponds to the point `(x, y)` in
   *         Cartesian coordinates.
   */
  @library
  def atan2(y: Double, x: Double): Double = {
    FdLibm.Atan2.compute(y, x)
  }.ensuring( res =>
    (res.isNaN == (y.isNaN || x.isNaN))
      && ((!y.isNaN && !x.isNaN) ==> (-Pi <= res && res <= Pi))
      && ((y.isPositive && x.isPositive) ==> (res.isPositive && res <= Pi / 2))
      && ((y.isPositive && x.isNegative) ==> (Pi / 2 <= res && res <= Pi))
      && ((y.isNegative && x.isNegative) ==> (-Pi <= res && res <= -Pi / 2))
      && ((y.isNegative && x.isPositive) ==> (-Pi / 2 <= res && res.isNegative))
      && ((y.isZero && y.isPositive && x.isPositive) ==> (res == y))
      && ((y.isZero && y.isPositive && x.isNegative) ==> (res == Pi))
      && ((y.isZero && y.isNegative && x.isNegative) ==> (res == -Pi))
      && ((y.isPosInfinity && x.isPosInfinity) ==> (res == Pi / 4))
      && ((y.isNegInfinity && x.isPosInfinity) ==> (res == - Pi / 4))
      && ((y.isPosInfinity && x.isNegInfinity) ==> (res == 3 * Pi / 4))
      && ((y.isNegInfinity && x.isNegInfinity) ==> (res == - 3 * Pi / 4))
      && ((y.isFinite && y.isPositive && x.isPosInfinity) ==> (res.isZero && y.isPositive))
      && ((y.isFinite && y.isNegative && x.isPosInfinity) ==> (res.isZero && y.isNegative))
      && ((y.isFinite && y.isPositive && x.isNegInfinity) ==> (res == Pi))
      && ((y.isFinite && y.isNegative && x.isNegInfinity) ==> (res == - Pi))
      && ((y.isPosInfinity && x.isFinite && !x.isZero) ==> (res == Pi / 2))
      && ((y.isNegInfinity && x.isFinite && !x.isZero) ==> (res == -Pi / 2))
  )

  /** Returns the square root of the sum of the squares of both given `Double`
   * values without intermediate underflow or overflow.
   *
   * The ''r'' component of the point `(r, theta)` in polar
   * coordinates that corresponds to the point `(x, y)` in
   * Cartesian coordinates.
   *
   * @group polar-coords
   */
  @library
  def hypot(x: Double, y: Double): Double = {
    FdLibm.Hypot.compute(x, y)
  }.ensuring(res =>
    ((x.isInfinity || y.isInfinity) ==> res.isPosInfinity) &&
    (res.isNaN == (!x.isInfinity && !y.isInfinity && (x.isNaN || y.isNaN))) &&
    (!res.isNaN ==> res.isPositive) &&
    ((x.isZero && !y.isNaN) ==> (res == stainless.math.abs(y))) &&
    ((y.isZero && !x.isNaN) ==> (res == stainless.math.abs(x)))
  )

  // -----------------------------------------------------------------------
  // rounding functions
  // -----------------------------------------------------------------------


  @ignore
  def ceil(x: Double) = scala.math.ceil(x)

  @ignore
  def floor(x: Double) = scala.math.floor(x)

  /** Returns the `Double` value that is closest in value to the
   * argument and is equal to a mathematical integer.
   *
   * @param x a `Double` value
   * @return the closest floating-point value to a that is equal to a
   *         mathematical integer.
   */
  @ignore
  def rint(x: Double) = scala.math.rint(x)

  //MISSING: round()


  @library
  def abs(n: BigInt) = if (n < 0) -n else n

  @library
  def abs(a: Int) = if (a < 0) -a else a

  @library
  def abs(a: Long) = if (a < 0) -a else a

  @ignore
  def abs(x: Float) = scala.math.abs(x)

  @ignore
  def abs(x: Double) = scala.math.abs(x)


  @library
  def max(i1: BigInt, i2: BigInt) = if (i1 >= i2) i1 else i2

  @library
  def max(i1: BigInt, i2: BigInt, i3: BigInt) = if (i1 >= i2) i1 else if (i2 >= i3) i2 else i3

  @library
  def max(i1: Nat, i2: Nat) = if (i1 >= i2) i1 else i2

  @library
  def max(i1: Int, i2: Int) = if (i1 >= i2) i1 else i2

  @library
  def max(i1: Long, i2: Long) = if (i1 >= i2) i1 else i2

  @ignore
  def max(x: Float, y: Float): Float = scala.math.max(x, y)

  @ignore
  def max(x: Double, y: Double): Double = scala.math.max(x, y)



  @library
  def min(i1: Nat, i2: Nat) = if (i1 <= i2) i1 else i2

  @library
  def min(i1: BigInt, i2: BigInt) = if (i1 <= i2) i1 else i2

  @library
  def min(i1: Int, i2: Int) = if (i1 <= i2) i1 else i2

  @library
  def min(i1: Long, i2: Long) = if (i1 <= i2) i1 else i2

  @ignore
  def min(x: Float, y: Float): Float = scala.math.min(x, y)

  @ignore
  def min(x: Double, y: Double): Double = scala.math.min(x, y)

  @library
  def signum(x: Int): Int = (x >> 31) | (-x >>> 31)

  @library
  def signum(x: Long): Long = ((x >> 63) | (-x >>> 63)).toInt

  @library
  def signum(d: Double): Double = if d.isNaN || d == 0.0 then d
  else copySign(1.0, d)

  @library
  def floorDiv(x: Int, y: Int): Int = {
    require(y != 0)
    val q = x / y
    // if the signs are different and modulo not zero, round down
    if (x ^ y) < 0 && (q * y != x) then q - 1 else q
  }

  @library
  def floorDiv(x: Long, y: Long): Long = {
    require(y != 0)
    val q: Long = x / y
    // if the signs are different and modulo not zero, round down
    if (x ^ y) < 0 && (q * y != x) then q - 1 else q
  }

  @library
  def floorMod(x: Int, y: Int): Int = {
    require(y != 0)
    val r: Int = x % y
    // if the signs are different and modulo not zero, adjust result
    if (x ^ y) < 0 && r != 0 then r + y else r
  }

  @library
  def floorMod(x: Long, y: Long): Long = {
    require(y != 0)
    val r: Long = x % y
    // if the signs are different and modulo not zero, adjust result
    if (x ^ y) < 0 && r != 0 then r + y else r
  }

  @library
  def copySign(magnitude: Double, sign: Double): Double = {
    require(!magnitude.isNaN)
    require(!sign.isNaN)
    java.lang.Double.longBitsToDouble(
      (java.lang.Double.doubleToLongBits(sign) & DoubleConsts.SIGN_BIT_MASK) |
      (java.lang.Double.doubleToLongBits(magnitude) & (DoubleConsts.EXP_BIT_MASK | DoubleConsts.SIGNIF_BIT_MASK)))
  }

  @library
  def copySign(magnitude: Float, sign: Float): Float = {
    require(!magnitude.isNaN)
    require(!sign.isNaN)
    java.lang.Float.intBitsToFloat(
      (java.lang.Float.floatToIntBits(sign) & FloatConsts.SIGN_BIT_MASK) |
      (java.lang.Float.floatToIntBits(magnitude) & (FloatConsts.EXP_BIT_MASK | FloatConsts.SIGNIF_BIT_MASK)))
  }

  @library
  def nextAfter(start: Double, direction: Double): Double = {
    if start.isNaN || direction.isNaN then
      Double.NaN
    else if start > direction then // descending
      if start != 0.0d then
        val transducer = java.lang.Double.doubleToLongBits(start)
        java.lang.Double.longBitsToDouble(transducer + (if (transducer > 0L) -1L
        else 1L))
      else  // start == 0.0d && direction < 0.0d
        -Double.MinValue
    else if (start < direction) then // ascending
      // Add +0.0 to get rid of a -0.0 (+0.0 + -0.0 => +0.0)
      // then bitwise convert start to integer.
      val transducer = java.lang.Double.doubleToLongBits(start + 0.0d)
      java.lang.Double.longBitsToDouble(transducer + (if (transducer >= 0L) 1L
      else -1L))
    else direction
  }

  @library
  def nextAfter(start: Float, direction: Double): Float = {
    if start.isNaN || direction.isNaN then
      Float.NaN
    else if start > direction then // descending
      if start != 0.0f then
        val transducer: Int = java.lang.Float.floatToIntBits(start)
        java.lang.Float.intBitsToFloat(transducer + (if (transducer > 0) -1
        else 1))
      else // start == 0.0d && direction < 0.0d
        -Float.MinValue
    else if (start < direction) then // ascending
      // Add +0.0 to get rid of a -0.0 (+0.0 + -0.0 => +0.0)
      // then bitwise convert start to integer.
      val transducer: Int = java.lang.Float.floatToIntBits(start + 0.0f)
      java.lang.Float.intBitsToFloat(transducer + (if (transducer >= 0) 1
      else -1))
    else direction.toFloat
  }

  @library
  def nextUp(d: Double): Double = {
    if d.isNaN || d.isPosInfinity then d
    else
      // Add +0.0 to get rid of a -0.0 (+0.0 + -0.0 => +0.0).
      val transducer = java.lang.Double.doubleToLongBits(d + 0.0D)
      java.lang.Double.longBitsToDouble(transducer + (if (transducer >= 0L) 1L else -1L))
  }

  @library
  def nextUp(f: Float): Float = {
    if f.isNaN || f.isPosInfinity then f
    else
      // Add +0.0 to get rid of a -0.0 (+0.0 + -0.0 => +0.0).
      val transducer = java.lang.Float.floatToIntBits(f + 0.0F)
      java.lang.Float.intBitsToFloat(transducer + (if (transducer >= 0) 1 else -1))
  }

  @library
  def nextDown(d: Double): Double = {
    if d.isNaN || d.isNegInfinity then d
    else
      if d == 0.0 then -Double.MinValue
      else java.lang.Double.longBitsToDouble(java.lang.Double.doubleToLongBits(d) + (if (d > 0.0d) -1L else +1L))
  }

  @library
  def nextDown(f: Float): Float = {
    if f.isNaN || f.isNegInfinity then f
    else
      if f == 0.0f then -Float.MinValue
      else java.lang.Float.intBitsToFloat(java.lang.Float.floatToIntBits(f) + (if f > 0.0 then -1 else +1));
  }

  private val twoToTheDoubleScaleUp: Double = powerOfTwoD(512)
  private val twoToTheDoubleScaleDown: Double = powerOfTwoD(-512)

  @library
  def scalb(d: Double, scaleFactor: Int): Double = {
    val MAX_SCALE = DoubleConsts.MAX_EXPONENT + -DoubleConsts.MIN_EXPONENT + DoubleConsts.SIGNIFICAND_WIDTH + 1
    val scale_increment: Int = if scaleFactor < 0 then -512 else 512
    val exp_delta =  if scaleFactor < 0 then twoToTheDoubleScaleDown else twoToTheDoubleScaleUp
    val newScaleFactor = if scaleFactor < 0 then max(scaleFactor, -MAX_SCALE) else min(scaleFactor, MAX_SCALE)
    val t = (newScaleFactor >> 9 - 1) >>> 32 - 9
    val exp_adjust = ((newScaleFactor + t) & (512 - 1)) - t
    var dVar: Double = d * powerOfTwoD(exp_adjust)
    var scaleFactorVar = newScaleFactor - exp_adjust
    (while (scaleFactorVar != 0) {
      decreases(abs(scaleFactorVar))
      dVar = dVar * exp_delta
      scaleFactorVar = scaleFactorVar - scale_increment
    }).invariant(
      (dVar.isNaN == d.isNaN)
      && (scaleFactorVar % 512 == 0)
      && (scale_increment < 0 ==> scaleFactorVar <= 0)
      && (scale_increment > 0 ==> scaleFactorVar >= 0)
      && (-MAX_SCALE <= scaleFactorVar && scaleFactorVar <= MAX_SCALE)
    )
    dVar
  }.ensuring( res =>
    res.isNaN == d.isNaN
    && (d.isPosInfinity ==> res.isPosInfinity)
    && (d.isNegInfinity ==> res.isNegInfinity)
    && (d.isZero ==> (res == d))
    && (d.isPositive == res.isPositive)
    && (d.isNegative == res.isNegative)
    && ((scaleFactor == 0 && !d.isNaN) ==> (d == res))
    && ((scaleFactor >= 0 && !d.isNaN) ==> (math.abs(res) >= math.abs(d)))
    && ((scaleFactor <= 0 && !d.isNaN) ==> (math.abs(res) <= math.abs(d)))
  )

  // -----------------------------------------------------------------------
  // root functions
  // -----------------------------------------------------------------------

  /** Returns the square root of a `Double` value.
   *
   * @param x the number to take the square root of
   * @return the value √x
   */
  @ignore
  def sqrt(a: Double): Double = {
    scala.math.sqrt(a)
  }

  /** Returns the cube root of the given `Double` value.
   *
   * @param x the number to take the cube root of
   * @return the value ∛x
   */
  @library
  def cbrt(x: Double): Double = {
    FdLibm.Cbrt.compute(x)
  }.ensuring(res =>
    (res.isNaN == x.isNaN) &&
    (x.isPosInfinity ==> res.isPosInfinity) &&
    (x.isNegInfinity ==> res.isNegInfinity) &&
    (x.isZero == res.isZero) &&
    ((x == 1) ==> (res == 1)) &&
    ((x == -1) ==> (res == -1)) &&
    (x.isPositive == res.isPositive) &&
    (x.isNegative == res.isNegative) &&
    ((x.isFinite && abs(x) > 1) ==> abs(res) < abs(x)) &&
    ((x.isFinite && !x.isZero && abs(x) < 1) ==> abs(res) > abs(x))
  )


  // -----------------------------------------------------------------------
  // exponential functions
  // -----------------------------------------------------------------------

  /** Returns the value of the first argument raised to the power of the
   * second argument.
   *
   * @param x the base.
   * @param y the exponent.
   * @return the value `x^y^`.
   */
  @library
  def pow(x: Double, y: Double) = {
    FdLibm.Pow.compute(x, y)
  }.ensuring( res =>
    (y.isZero ==> (res == 1.0))
    && ((!x.isNaN && y.isFinite && y == 1.0) ==> (res == x))
    && (y.isNaN ==> res.isNaN)
    && ((x.isNaN && !y.isZero) ==> res.isNaN)
    && (((x.isFinite && (x < -1.0d || x > 1.0d)) && y.isPositive && y.isInfinity) ==> (res.isPositive && res.isInfinity))
    && ((x.isFinite && -1.0d < x && x < 1.0d && y.isNegative && y.isInfinity) ==> (res.isPositive && res.isInfinity))
    && (((x.isFinite && (x < -1.0d || x > 1.0d)) && y.isNegative && y.isInfinity) ==> (res.isPositive && res.isZero))
    && ((x.isFinite && -1.0d < x && x < 1.0d && y.isPositive && y.isInfinity) ==> (res.isPositive && res.isZero))
    && (((x.isFinite && (x == 1.0d || x == -1.0d)) && y.isInfinity) ==> res.isNaN)
    && ((x.isPositive && x.isZero && !y.isNaN &&y > 0) ==> (res.isPositive && res.isZero))
    && ((x.isPositive && x.isInfinity && !y.isNaN && y < 0) ==> (res.isPositive && res.isZero))
    && ((x.isPositive && x.isZero && !y.isNaN && y < 0) ==> (res.isPositive && res.isInfinity))
    && ((x.isPositive && x.isInfinity && !y.isNaN && y > 0) ==> (res.isPositive && res.isInfinity))
    && ((!x.isNaN && y.isFinite && y == 2) ==> res.isPositive)
  )


  /** Returns Euler's number `e` raised to the power of a `Double` value.
   *
   *  @param  x the exponent to raise `e` to.
   *  @return the value `e^a^`, where `e` is the base of the natural
   *          logarithms.
   */
  @library
  def exp(x: Double): Double = {
    FdLibm.Exp.compute(x)
  }.ensuring(res =>
    res.isNaN == x.isNaN
      && (x.isPosInfinity ==> res.isPosInfinity)
      && (x.isNegInfinity ==> (res.isZero && res.isPositive))
      && (x.isZero ==> (res == 1))
      && ((!x.isNaN && x.isPositive) ==> res >= 1) // Converse does not hold: x = -7.458340731200206E-155
      && ((!x.isNaN && x.isNegative) ==> (0 <= res && res <= 1))
  )

  /** Returns `exp(x) - 1`.
   */
  @library
  def expm1(x: Double): Double = {
    FdLibm.Expm1.compute(x)
  }.ensuring(res =>
    res.isNaN == x.isNaN
      && (x.isPosInfinity ==> res.isPosInfinity)
      && (x.isNegInfinity ==> (res == -1))
      && (x.isZero ==> (res == 0))
      && ((!x.isNaN && x.isPositive) ==> res >= 0)
      && ((!x.isNaN && x.isNegative) ==> (-1 <= res && res <= 0))
  )

  @library
  def getExponent(f: Float): Int = {
    require(!f.isNaN)
    ((java.lang.Float.floatToIntBits(f) & FloatConsts.EXP_BIT_MASK) >> (FloatConsts.SIGNIFICAND_WIDTH - 1)) - FloatConsts.EXP_BIAS
  }

  @library
  def getExponent(d: Double): Int = {
    require(!d.isNaN)
    (((java.lang.Double.doubleToLongBits(d) & DoubleConsts.EXP_BIT_MASK) >> (DoubleConsts.SIGNIFICAND_WIDTH - 1)) - DoubleConsts.EXP_BIAS).toInt
  }


  // -----------------------------------------------------------------------
  // logarithmic functions
  // -----------------------------------------------------------------------

  /** Returns the natural logarithm of a `Double` value.
   *
   * @param x the number to take the natural logarithm of
   * @return the value `logₑ(x)` where `e` is Eulers number
   */
  @library
  def log(x: Double): Double = {
    FdLibm.Log.compute(x)
  }.ensuring( res =>
    (res.isNaN == (x.isNaN || x < 0))
      && (x.isZero == res.isNegInfinity)
      && ((x.isFinite && x == 1.0) == (res.isZero && res.isPositive))
      && ((!x.isNaN && x >= 1.0) == res.isPositive)
      && (res.isNegative == (x.isFinite && 0.0 <= x && x < 1.0))
      && ((!x.isNaN && x >= 0) ==> res <= x - 1)
      && (x.isPosInfinity == res.isPosInfinity)
  )
  @library
  def log1p(x: Double): Double = {
    FdLibm.Log1p.compute(x)
  }.ensuring( res =>
    (res.isNaN == (x.isNaN || x < -1))
      && ((x.isFinite && x == -1.0) == res.isNegInfinity)
      && ((x.isZero && x.isPositive) == (res.isZero && res.isPositive))
      && ((x.isZero && x.isNegative) == (res.isZero && res.isNegative))
      && (x.isPositive == res.isPositive)
      && ((x.isNegative &&  x >= -1) == res.isNegative)
      && ((!x.isNaN && x >= -1) ==> res <= x)
      && (x.isPosInfinity == res.isPosInfinity)
  )

  /** Returns the base 10 logarithm of the given `Double` value.
   */
  @library
  def log10(x: Double): Double = {
    FdLibm.Log10.compute(x)
  }.ensuring( res =>
    (res.isNaN == (x.isNaN || x < 0))
      && (x.isZero == res.isNegInfinity)
      && ((x == 1.0) ==> (res.isZero && res.isPositive))
      && ((x >= 1.0) == res.isPositive)
      && (res.isNegative ==> (x < 1.0))
      && ((x.isFinite && x >= 0) ==> res < x)
      && (x.isPosInfinity == res.isPosInfinity)
  )

  // -----------------------------------------------------------------------
  // trigonometric functions
  // -----------------------------------------------------------------------

  /** Returns the hyperbolic sine of the given `Double` value.
   */
  @library
  def sinh(x: Double): Double = {
    FdLibm.Sinh.compute(x)
  }.ensuring(res =>
    res.isNaN == x.isNaN
      && (x.isPosInfinity ==> res.isPosInfinity)
      && (x.isNegInfinity ==> res.isNegInfinity)
      && (x.isZero ==> res.isZero)
      && (x.isPositive == res.isPositive)
      && (x.isNegative == res.isNegative)
  )

  /** Returns the hyperbolic cosine of the given `Double` value.
   */
  @library
  def cosh(x: Double): Double = {
    FdLibm.Cosh.compute(x)
  }.ensuring(res =>
    res.isNaN == x.isNaN
      && (!x.isNaN ==> res.isPositive)
      && (x.isInfinity ==> res.isPosInfinity)
      && (x.isZero ==> (res == 1.0))
  )

  /** Returns the hyperbolic tangent of the given `Double` value.
   */
  @library
  def tanh(x: Double): Double = {
    FdLibm.Tanh.compute(x)
  }.ensuring(res =>
    (x.isNaN == x.isNaN)
      && (!x.isNaN ==> (-1 <= res && res <= 1))
      && (x.isPositive ==> res >= 0)
      && (x.isNegative ==> res <= 0)
      && (x.isNegInfinity ==> (res == -1))
      && (x.isPosInfinity ==> (res == 1))
      && (x.isZero ==> res.isZero)
  )

  // -----------------------------------------------------------------------
  // miscellaneous functions
  // -----------------------------------------------------------------------

  /** Returns the size of an ulp of the given `Double` value.
   */
  @library
  def ulp(d: Double): Double = {
    require(!d.isNaN)
    var exp = getExponent(d)
    if exp == DoubleConsts.MAX_EXPONENT + 1 then abs(d) // NaN or infinity
    else if exp == DoubleConsts.MIN_EXPONENT - 1 then Double.MinValue // zero or subnormal
    else
      // ulp(x) is usually 2^(SIGNIFICAND_WIDTH-1)*(2^ilogb(x))
      exp = exp - (DoubleConsts.SIGNIFICAND_WIDTH - 1)
      if exp >= DoubleConsts.MIN_EXPONENT then powerOfTwoD(exp)
      else
        // return a subnormal result; left shift integer
        // representation of Double.MIN_VALUE appropriate
        // number of positions
        java.lang.Double.longBitsToDouble(1L << (exp - (DoubleConsts.MIN_EXPONENT - (DoubleConsts.SIGNIFICAND_WIDTH - 1))))
  }

  /** Returns the size of an ulp of the given `Float` value.
   */
  @library
  def ulp(f: Float): Float = {
    require(!f.isNaN)
    var exp = getExponent(f)
    if exp == FloatConsts.MAX_EXPONENT + 1 then abs(f) // NaN or infinity
    else if exp == FloatConsts.MIN_EXPONENT - 1 then Float.MinValue // zero or subnormal
    else
      // ulp(x) is usually 2^(SIGNIFICAND_WIDTH-1)*(2^ilogb(x))
      exp = exp - (FloatConsts.SIGNIFICAND_WIDTH - 1)
      if exp >= FloatConsts.MIN_EXPONENT then powerOfTwoF(exp)
      else
        // return a subnormal result; left shift integer
        // representation of Double.MIN_VALUE appropriate
        // number of positions
        java.lang.Float.intBitsToFloat(1 << (exp - (FloatConsts.MIN_EXPONENT - (FloatConsts.SIGNIFICAND_WIDTH - 1))))
  }

  // MISSING: IEEEremainder

  @library
  def addExact(x: Int, y: Int): Int =
    require(((x ^ wrapping(x + y)) & (y ^ wrapping(x + y))) >= 0)
    x + y

  @library
  def addExact(x: Long, y: Long): Long =
    require(((x ^ wrapping(x + y)) & (y ^ wrapping(x + y))) >= 0)
    x + y

  @library
  def subtractExact(x: Int, y: Int): Int = {
    require(((x ^ y) & (x ^ wrapping(x - y))) >= 0)
    x - y
  }

  @library
  def subtractExact(x: Long, y: Long): Long = {
    require(((x ^ y) & (x ^ wrapping(x - y))) >= 0)
    x - y
  }

  @library
  def multiplyExact(x: Int, y: Int): Int = {
    require(wrapping((x.toLong * y.toLong).toInt).toLong == wrapping(x.toLong * y.toLong))
    x * y
  }

  @library
  def multiplyExact(x: Long, y: Long): Long = {
    require(((wrapping(abs(x)) | wrapping(abs(y))) >>> 31 == 0) || !(((y != 0) && (wrapping(x * y / y) != x)) || (x == Long.MinValue && y == -1)))
    x * y
  }

  @library
  def incrementExact(a: Int): Int = {
    require(a < Int.MaxValue)
    a + 1
  }

  @library
  def incrementExact(a: Long): Long = {
    require(a < Long.MaxValue)
    a + 1
  }

  @library
  def decrementExact(a: Int): Int = {
    require(a > Int.MinValue)
    a - 1
  }

  @library
  def decrementExact(a: Long): Long = {
    require(a > Long.MinValue)
    a - 1
  }

  @library
  def negateExact(a: Int): Int = {
    require(a != Int.MinValue)
    -a
  }

  @library
  def negateExact(a: Long): Long = {
    require(a != Long.MinValue)
    -a
  }

  @library
  def toIntExact(value: Long): Int = {
    require(wrapping(value.toInt) == value)
    value.toInt
  }

  // -----------------------------------------------------------------------
  // Stainless specific
  // -----------------------------------------------------------------------


  /** Disable overflow checks within `body`.
    *
    * This is equivalent to setting `--strict-arithmetic=false` for `body` only.
    */
  @ignore
  def wrapping[A](body: A): A = body


  @library
  implicit def bigIntToNat(b: BigInt): Nat = {
    require(b >= 0)
    Nat(b)
  }

  // -----------------------------------------------------------------------
  // helper functions
  // -----------------------------------------------------------------------


  @library
  private def powerOfTwoD(n: Int): Double = {
    require( DoubleConsts.MIN_EXPONENT <= n && n <= DoubleConsts.MAX_EXPONENT)
    java.lang.Double.longBitsToDouble(((n.toLong + DoubleConsts.EXP_BIAS.toLong) << (DoubleConsts.SIGNIFICAND_WIDTH - 1)) & DoubleConsts.EXP_BIT_MASK)
  }

  @library
  private def powerOfTwoF(n: Int): Float = {
    assert(n >= FloatConsts.MIN_EXPONENT && n <= FloatConsts.MAX_EXPONENT)
    java.lang.Float.intBitsToFloat(((n + FloatConsts.EXP_BIAS) << (FloatConsts.SIGNIFICAND_WIDTH - 1)) & FloatConsts.EXP_BIT_MASK)
  }




}

