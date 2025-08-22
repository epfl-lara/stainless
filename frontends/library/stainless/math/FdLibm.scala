package stainless
package math

import stainless.annotation.*
import stainless.lang.*

private object LongHelpers {
  @library
  def compare(x: Long, y: Long): Int = if x < y then -1 else if x == y then 0 else 1
  @library
  def compareUnsigned(x: Long, y: Long): Int = compare(x + Long.MinValue, y + Long.MinValue)
}

private object IntHelpers {
  @library
  def compare(x: Int, y: Int): Int = if x < y then -1 else if x == y then 0 else 1

  @library
  def compareUnsigned(x: Int, y: Int): Int = compare(x + Int.MinValue, y + Int.MinValue)
}

object FdLibm {

  // Constants used by multiple algorithms
  private val TWO24: Double = java.lang.Double.longBitsToDouble(0x4170000000000000L) // 1.67772160000000000000e+07
  private val TWO54: Double = java.lang.Double.longBitsToDouble(0x4350000000000000L) // 1.80143985094819840000e+16
  private val HUGE = 1.0e+300

  /*
   * Constants for bit-wise manipulation of IEEE 754 double
   * values. These constants are for the high-order 32-bits of a
   * 64-bit double value: 1 sign bit as the most significant bit,
   * followed by 11 exponent bits, and then the remaining bits as
   * the significand.
   */
  private val SIGN_BIT: Int = 0x8000_0000
  private val EXP_BITS: Int = 0x7ff0_0000
  private val EXP_SIGNIF_BITS: Int = 0x7fff_ffff

  /**
   * Return the low-order 32 bits of the double argument as an int.
   */
  @library
  private def __LO(x: Double): Int = {
    require(!x.isNaN)
    val transducer = java.lang.Double.doubleToLongBits(x)
    stainless.math.wrapping(transducer.toInt)
  }

  /**
   * Return a double with its low-order bits of the second argument
   * and the high-order bits of the first argument..
   */
  @library
  private def __LO(x: Double, low: Int) = {
    require(!x.isNaN)
    val transX = java.lang.Double.doubleToLongBits(x)
    java.lang.Double.longBitsToDouble((transX & 0xFFFF_FFFF_0000_0000L) | (low & 0x0000_0000_FFFF_FFFFL))
  }

  /**
   * Return the high-order 32 bits of the double argument as an int.
   */
  @library
  private def __HI(x: Double): Int = {
    require(!x.isNaN)
    val transducer = java.lang.Double.doubleToLongBits(x)
    (transducer >> 32).toInt
  }

  /**
   * Return a double with its high-order bits of the second argument
   * and the low-order bits of the first argument..
   */
  @library
  private def __HI(x: Double, high: Int): Double = {
    require(!x.isNaN)
    val transX = java.lang.Double.doubleToLongBits(x)
    java.lang.Double.longBitsToDouble((transX & 0x0000_0000_FFFF_FFFFL) | high.toLong << 32)
  }

  object Asin {
    private val pio2_hi = java.lang.Double.longBitsToDouble(0x3ff921fb54442d18L)
    private val pio2_lo = java.lang.Double.longBitsToDouble(0x3c91a62633145c07L)
    private val pio4_hi = java.lang.Double.longBitsToDouble(0x3fe921fb54442d18L)
    private val pS0 = java.lang.Double.longBitsToDouble(0x3fc5555555555555L)
    private val pS1 = java.lang.Double.longBitsToDouble(0xbfd4d61203eb6f7dL)
    private val pS2 = java.lang.Double.longBitsToDouble(0x3fc9c1550e884455L)
    private val pS3 = java.lang.Double.longBitsToDouble(0xbfa48228b5688f3bL)
    private val pS4 = java.lang.Double.longBitsToDouble(0x3f49efe07501b288L)
    private val pS5 = java.lang.Double.longBitsToDouble(0x3f023de10dfdf709L)
    private val qS1 = java.lang.Double.longBitsToDouble(0xc0033a271c8a2d4bL)
    private val qS2 = java.lang.Double.longBitsToDouble(0x40002ae59c598ac8L)
    private val qS3 = java.lang.Double.longBitsToDouble(0xbfe6066c1b8d0159L)
    private val qS4 = java.lang.Double.longBitsToDouble(0x3fb3b8c5b12e9282L)

    @opaque @library
    def compute(x: Double): Double = {
      if x.isNaN then Double.NaN
      else
        val hx = __HI(x)
        val ix = hx & EXP_SIGNIF_BITS
        if ix >= 0x3ff0_0000 then // |x| >= 1
          if ((ix - 0x3ff0_0000) | __LO(x)) == 0 then x * pio2_hi + x * pio2_lo // asin(1) = +-pi/2 with inexact
          else (x - x) / (x - x) // asin(|x| > 1) is NaN
        else if ix < 0x3fe0_0000 then // |x| < 0.5
          if ix < 0x3e40_0000 && HUGE + x > 1.0 then x // return x with inexact if x != 0
          else
            val t = if ix < 0x3e40_0000 then 0 else x * x
            val p = t * (pS0 + t * (pS1 + t * (pS2 + t * (pS3 + t * (pS4 + t * pS5)))))
            val q = 1.0 + t * (qS1 + t * (qS2 + t * (qS3 + t * qS4)))
            val w = p / q
            x + x * w
        else
          // 1 > |x| >= 0.5
          val t = (1.0 - stainless.math.abs(x)) * 0.5
          val p = t * (pS0 + t * (pS1 + t * (pS2 + t * (pS3 + t * (pS4 + t * pS5)))))
          val q = 1.0 + t * (qS1 + t * (qS2 + t * (qS3 + t * qS4)))
          val s = stainless.math.sqrt(t)
          val w = if ix >= 0x3FEF_3333 then p / q else __LO(s, 0)
          val p2 = if ix >= 0x3FEF_3333 then p else 2.0 * s * (p / q) - (pio2_lo - 2.0 * ((t - w * w) / (s + w)))
          val q2 = if ix >= 0x3FEF_3333 then q else pio4_hi - 2.0 * w
          val t2 = if ix >= 0x3FEF_3333 then pio2_hi - (2.0*(s + s*w) - pio2_lo) else pio4_hi - (p2 - q2)
          if hx > 0 then t2 else -t2
    }.ensuring(res =>
      ((x.isNaN || x < -1.0d || x > 1.0d) == res.isNaN)
        && ((x.isPositive && x.isZero) == (res.isPositive && res.isZero))
        && ((x.isNegative && x.isZero) == (res.isNegative && res.isZero))
        && ((x.isFinite && x == -1.0d) == (res.isFinite && res == -stainless.math.Pi / 2))
        && ((x.isFinite && x == 1.0d) == (res.isFinite && res == stainless.math.Pi / 2))
        && ((x.isFinite && -1.0d <= x && x <= 1.0d) == (res.isFinite && -stainless.math.Pi / 2 <= res && res <= stainless.math.Pi / 2))
    )
  }

  object Acos {
    private val pio2_hi = java.lang.Double.longBitsToDouble(0x3ff921fb54442d18L)
    private val pio2_lo = java.lang.Double.longBitsToDouble(0x3c91a62633145c07L)
    private val pS0 = java.lang.Double.longBitsToDouble(0x3fc5555555555555L)
    private val pS1 = java.lang.Double.longBitsToDouble(0xbfd4d61203eb6f7dL)
    private val pS2 = java.lang.Double.longBitsToDouble(0x3fc9c1550e884455L)
    private val pS3 = java.lang.Double.longBitsToDouble(0xbfa48228b5688f3bL)
    private val pS4 = java.lang.Double.longBitsToDouble(0x3f49efe07501b288L)
    private val pS5 = java.lang.Double.longBitsToDouble(0x3f023de10dfdf709L)
    private val qS1 = java.lang.Double.longBitsToDouble(0xc0033a271c8a2d4bL)
    private val qS2 = java.lang.Double.longBitsToDouble(0x40002ae59c598ac8L)
    private val qS3 = java.lang.Double.longBitsToDouble(0xbfe6066c1b8d0159L)
    private val qS4 = java.lang.Double.longBitsToDouble(0x3fb3b8c5b12e9282L)

    @opaque @library
    def compute(x: Double): Double = {
      if x.isNaN then Double.NaN
      else
        val hx = __HI(x)
        val ix = hx & EXP_SIGNIF_BITS
        if ix >= 0x3ff0_0000 then // |x| >= 1
          if ((ix - 0x3ff0_0000) | __LO(x)) == 0 then // |x| == 1
            if hx > 0 then 0.0 else stainless.math.Pi + 2.0 * pio2_lo
          else (x - x) / (x - x) // acos(|x| > 1) is NaN
        else if ix < 0x3fe0_0000 then // |x| < 0.5
          if ix <= 0x3c60_0000 then // if |x| < 2**-57
            pio2_hi + pio2_lo
          else
            val z = x * x
            val p = z * (pS0 + z * (pS1 + z * (pS2 + z * (pS3 + z * (pS4 + z * pS5)))))
            val q = 1.0 + z * (qS1 + z * (qS2 + z * (qS3 + z * qS4)))
            val r = p / q
            pio2_hi - (x - (pio2_lo - x * r))
        else if hx < 0 then // x < -0.5
          val z = (1.0 + x) * 0.5
          val p = z * (pS0 + z * (pS1 + z * (pS2 + z * (pS3 + z * (pS4 + z * pS5)))))
          val q = 1.0 + z * (qS1 + z * (qS2 + z * (qS3 + z * qS4)))
          val s = stainless.math.sqrt(z)
          val r = p / q
          val w = r * s - pio2_lo
          stainless.math.Pi - 2.0 * (s + w)
        else  // x > 0.5
          val z = (1.0 - x) * 0.5
          val s = stainless.math.sqrt(z)
          val df = __LO(s, 0)
          val c = (z - df * df) / (s + df)
          val p = z * (pS0 + z * (pS1 + z * (pS2 + z * (pS3 + z * (pS4 + z * pS5)))))
          val q = 1.0 + z * (qS1 + z * (qS2 + z * (qS3 + z * qS4)))
          val r = p / q
          val w = r * s + c
          2.0 * (df + w)
    }.ensuring(res =>
      ((x.isNaN || x < -1.0d || x > 1.0d) == res.isNaN)
        && ((x.isFinite && x == 1.0d) ==> (res.isPositive && res.isZero))
        && ((x.isFinite && x == -1.0d) == (res.isFinite && res == stainless.math.Pi))
        && (x.isZero ==> (res == stainless.math.Pi / 2))
        && ((x.isFinite && -1.0d <= x && x <= 1.0d) == (res.isFinite && res.isPositive && 0 <= res && res <= stainless.math.Pi))
    )
  }

  object Atan {
    private val atanhi0 = java.lang.Double.longBitsToDouble(0x3fddac670561bb4fL) // atan(0.5)hi 4.63647609000806093515e-01
    private val atanhi1 = java.lang.Double.longBitsToDouble(0x3fe921fb54442d18L)
    private val atanhi2 = java.lang.Double.longBitsToDouble(0x3fef730bd281f69bL)
    private val atanhi3 = java.lang.Double.longBitsToDouble(0x3ff921fb54442d18L)

    private val atanlo0 = java.lang.Double.longBitsToDouble(0x3c7a2b7f222f65e2L) // atan(0.5)lo 2.26987774529616870924e-17
    private val atanlo1 = java.lang.Double.longBitsToDouble(0x3c81a62633145c07L)
    private val atanlo2 = java.lang.Double.longBitsToDouble(0x3c7007887af0cbbdL)
    private val atanlo3 = java.lang.Double.longBitsToDouble(0x3c91a62633145c07L)

    private val aT0 = java.lang.Double.longBitsToDouble(0x3fd555555555550dL)
    private val aT1 = java.lang.Double.longBitsToDouble(0xbfc999999998ebc4L)
    private val aT2 = java.lang.Double.longBitsToDouble(0x3fc24924920083ffL)
    private val aT3 = java.lang.Double.longBitsToDouble(0xbfbc71c6fe231671L)
    private val aT4 = java.lang.Double.longBitsToDouble(0x3fb745cdc54c206eL)
    private val aT5 = java.lang.Double.longBitsToDouble(0xbfb3b0f2af749a6dL)
    private val aT6 = java.lang.Double.longBitsToDouble(0x3fb10d66a0d03d51L)
    private val aT7 = java.lang.Double.longBitsToDouble(0xbfadde2d52defd9aL)
    private val aT8 = java.lang.Double.longBitsToDouble(0x3fa97b4b24760debL)
    private val aT9 = java.lang.Double.longBitsToDouble(0xbfa2b4442c6a6c2fL)
    private val aT10 = java.lang.Double.longBitsToDouble(0x3f90ad3ae322da11L)

    @opaque @library
    def compute(x: Double): Double = {
      if x.isNaN then Double.NaN else
        val hx = __HI(x)
        val ix = hx & EXP_SIGNIF_BITS
        if ix >= 0x4410_0000 then // if |x| >= 2^66
          if ix > EXP_BITS || (ix == EXP_BITS && (__LO(x) != 0)) then x + x // NaN
          else if hx > 0 then atanhi3 + atanlo3
          else -atanhi3 - atanlo3
        else
          if ix < 0x3fdc_0000 && ix < 0x3e20_0000 && HUGE + x > 1.0 then x
          else
            val id =
              if ix < 0x3fdc_0000 then -1 else
                if ix < 0x3ff3_0000 then
                  if ix < 0x3fe60000 then 0 else 1
                else if ix < 0x4003_8000 then 2 else 3



            val absX = stainless.math.abs(x)
            val newX =
              if ix < 0x3fdc_0000 then x else
                if ix < 0x3ff3_0000 then
                  if ix < 0x3fe60000 then (2.0 * absX - 1.0) / (2.0 + absX) else (absX - 1.0) / (absX + 1.0)
                else if ix < 0x4003_8000 then (absX - 1.5) / (1.0 + 1.5 * absX) else -1.0 / absX

            // end of argument reduction
            val z = newX * newX
            val w = z * z
            // break sum from i=0 to 10 aT[i]z**(i+1) into odd and even poly
            val s1 = z * (aT0 + w * (aT2 + w * (aT4 + w * (aT6 + w * (aT8 + w * aT10)))))
            val s2 = w * (aT1 + w * (aT3 + w * (aT5 + w * (aT7 + w * aT9))))
            if id < 0 then newX - newX * (s1 + s2)
            else
              val atanhiId = id match
                case 0 => atanhi0
                case 1 => atanhi1
                case 2 => atanhi2
                case 3 => atanhi3

              val atanloId = id match
                case 0 => atanlo0
                case 1 => atanlo1
                case 2 => atanlo2
                case 3 => atanlo3
              val z = atanhiId - ((newX * (s1 + s2) - atanloId) - newX)
              if hx < 0 then -z else z

    }.ensuring( res =>
      (x.isNaN == res.isNaN)
      && (x.isPositive == res.isPositive)
      && (x.isNegative == res.isNegative)
      && (x.isZero == res.isZero)
      && (!x.isNaN ==> (- Pi / 2 <= res && res <= Pi / 2))
      && (x.isPosInfinity ==> (res == Pi / 2))
      && (x.isNegInfinity ==> (res == -Pi / 2))
    )
  }

  object Atan2 {
    private val tiny = 1.0e-300
    private val pi_o_4 = java.lang.Double.longBitsToDouble(0x3fe921fb54442d18L)
    private val pi_o_2 = java.lang.Double.longBitsToDouble(0x3ff921fb54442d18L)
    private val pi_lo = java.lang.Double.longBitsToDouble(0x3ca1a62633145c07L)

    @opaque @library
    def compute(y: Double, x: Double): Double = {
      if x.isNaN || y.isNaN then x + y
      else
        val hx = __HI(x)
        val ix = hx & EXP_SIGNIF_BITS
        val lx = __LO(x)
        val hy = __HI(y)
        val iy = hy & EXP_SIGNIF_BITS
        val ly = __LO(y)


        if ((hx - 0x3ff0_0000) | lx) == 0 then Atan.compute(y) // x = 1.0
        else

          val m = ((hy >> 31) & 1) | ((hx >> 30) & 2) // 2*sign(x) + sign(y)

          // when y = 0
          if (iy | ly) == 0 then
            m match
              case 0 => y
              case 1 => y // atan(+/-0, +anything)  = +/-0
              case 2 => Pi + tiny // atan(+0,   -anything)  =  pi
              case 3 => -Pi - tiny // atan(-0,   -anything)  = -pi
          // when x = 0
          else if (ix | lx) == 0 then
            if hy < 0 then -pi_o_2 - tiny else pi_o_2 + tiny
          // when x is INF
          else if ix == EXP_BITS then
            if iy == EXP_BITS then
              m match
                case 0 => pi_o_4 + tiny // atan(+INF, +INF)
                case 1 => -pi_o_4 - tiny // atan(-INF, +INF)
                case 2 => 3.0 * pi_o_4 + tiny // atan(+INF, -INF)
                case 3 => -3.0 * pi_o_4 - tiny // atan(-INF, -INF)
            else
              m match
                case 0 => 0.0 // atan(+..., +INF)
                case 1 => -0.0 // atan(-..., +INF)
                case 2 => Pi + tiny // atan(+..., -INF)
                case 3 => -Pi - tiny // atan(-..., -INF)

          // when y is INF
          else if iy == EXP_BITS then
            if hy < 0 then -pi_o_2 - tiny else pi_o_2 + tiny
          else
            // compute y/x
            val k = (iy - ix) >> 20

            val z =
              if k > 60 then pi_o_2 + 0.5 * pi_lo // |y/x| >  2**60
              else if hx < 0 && k < -60 then 0.0 // |y|/x < -2**60
              else Atan.compute(abs(y / x))

            m match
              case 0 => z
              case 1 => -z
              case 2 => Pi - (z - pi_lo) // atan(+, -)
              case _ => (z - pi_lo) - Pi // atan(-, -), case 3
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
  }

  object Cbrt {
    // unsigned
    private val B1 = 715094163
    private val B2 = 696219795
    private val C = 19.0/35.0
    private val D = -864.0/1225.0
    private val E = 99.0/70.0
    private val F = 45.0/28.0
    private val G = 5.0/14.0

    @opaque @library
    def compute(x: Double): Double = {
      if !x.isFinite || x == 0.0  then x // Handles signed zeros properly
      else
        val sign = if x < 0.0 then -1.0 else 1.0
        val x_abs = stainless.math.abs(x) // x <- |x|

        // Rough cbrt to 5 bits
        val t =
          if x_abs < java.lang.Double.longBitsToDouble(0x10000000000000L) then
            // subnormal number
            val temp_t = 18014398509481984.0 * x_abs
            __HI(temp_t, __HI(temp_t) / 3 + B2)
          else
            val hx = __HI(x_abs) // high word of x
            __HI(0.0, hx / 3 + B1)

        // New cbrt to 23 bits, may be implemented in single precision
        val r = t * t / x_abs
        val s = C + r * t
        // Chopped to 20 bits and make it larger than cbrt(x)
        val t2 = __LO(t * (G + F / (s + E + D / s)), 0)
        val t3 = __HI(t2, __HI(t2) + 0x00000001)
        // One step newton iteration to 53 bits with error less than 0.667 ulps
        val r2 = x_abs / (t3 * t3)
        val w = t3 + t3
        // Restore the original sign bit
        sign * (t3 + t3 * ((r2 - t3) / (w + r2)))
      }.ensuring(res =>
        (res.isNaN == x.isNaN) &&
        (x.isPosInfinity ==> res.isPosInfinity) &&
        (x.isNegInfinity ==> res.isNegInfinity) &&
        (x.isZero == res.isZero) &&
        ((x == 1) ==> (res == 1)) &&
        ((x == -1) ==> (res == -1)) &&
        (x.isPositive == res.isPositive) &&
        (x.isNegative == res.isNegative) &&
        ((x.isFinite && stainless.math.abs(x) > 1) ==> stainless.math.abs(res) < stainless.math.abs(x)) &&
        ((x.isFinite && !x.isZero && stainless.math.abs(x) < 1) ==> stainless.math.abs(res) > stainless.math.abs(x))
      )
  }

  object Hypot {
    private val TWO_MINUS_600: Double = java.lang.Double.longBitsToDouble(0x1a70000000000000L)
    private val TWO_PLUS_600: Double = java.lang.Double.longBitsToDouble(0x6570000000000000L)

    @opaque @library
    def compute(x: Double, y: Double): Double = {
      val a = stainless.math.abs(x)
      val b = stainless.math.abs(y)
      if !a.isFinite || !b.isFinite then
        if a.isPosInfinity || b.isPosInfinity then Double.PositiveInfinity else a + b // Propagate NaN significand bits
      else
        var big = if b > a then b else a
        var small = if b > a then a else b
        var hbig = __HI(big) // high word of a
        var hsmall = __HI(small) // high word of b

        if hbig - hsmall > 0x3c00000 then big + small // x / y > 2**60
        else
          var k: Int = 0
          if (big > java.lang.Double.longBitsToDouble(0x5f300000ffffffffL)) {
            // scale a and b by 2**-600
            hbig -= 0x25800000
            hsmall -= 0x25800000
            big = big * TWO_MINUS_600
            small = small * TWO_MINUS_600
            k += 600
          }
          if small == 0 then big
          else
            if (small < java.lang.Double.longBitsToDouble(0x20b0000000000000L)) { // b < 2**-500
              if (small < stainless.DoubleConsts.MIN_NORMAL) { // subnormal b or 0 */
                val t1 = java.lang.Double.longBitsToDouble(0x7fd0000000000000L) // t1 = 2^1022
                small *= t1
                big *= t1
                k -= 1022
              }
              else { // scale a and b by 2^600
                hbig += 0x25800000 // a *= 2^600
                hsmall += 0x25800000 // b *= 2^600
                big = big * TWO_PLUS_600
                small = small * TWO_PLUS_600
                k -= 600
              }
            }
            // medium size a and b
            val w: Double = big - small

            val res: Double = if w > b then
              val t1 = __HI(0.0, hbig)
              stainless.math.sqrt(t1 * t1 - (small * (-small) - (big - t1) * (big + t1)))
            else
              val bigbig = big + big
              val y1: Double = __HI(0.0, hsmall)
              val y2: Double = small - y1
              val t1 = __HI(0.0, hbig + 0x00100000)
              stainless.math.sqrt(t1 * y1 - (w * (-w) - (t1 * y2 + (bigbig - t1) * b)))


            if k != 0 then stainless.math.powerOfTwoD(k) * res else res

    }.ensuring(res =>
      ((x.isInfinity || y.isInfinity) ==> res.isPosInfinity) &&
      (res.isNaN == (!x.isInfinity && !y.isInfinity && (x.isNaN || y.isNaN))) &&
      (!res.isNaN ==> res.isPositive) &&
      ((x.isZero && !y.isNaN) ==> (res == stainless.math.abs(y))) &&
      ((y.isZero && !x.isNaN) ==> (res == stainless.math.abs(x)))
    )
  }

  object Log {
    private val ln2_hi: Double = java.lang.Double.longBitsToDouble(0x3fe62e42fee00000L)// 6.93147180369123816490e-01
    private val ln2_lo = java.lang.Double.longBitsToDouble(0x3dea39ef35793c76L) // 1.90821492927058770002e-10
    private val Lg1 = java.lang.Double.longBitsToDouble(0x3fe5555555555593L) // 6.666666666666735130e-01
    private val Lg2 = java.lang.Double.longBitsToDouble(0x3fd999999997fa04L) // 3.999999999940941908e-01
    private val Lg3 = java.lang.Double.longBitsToDouble(0x3fd2492494229359L) // 2.857142874366239149e-01
    private val Lg4 = java.lang.Double.longBitsToDouble(0x3fcc71c51d8e78afL)  // 2.222219843214978396e-01
    private val Lg5 = java.lang.Double.longBitsToDouble(0x3fc7466496cb03deL) // 1.818357216161805012e-01
    private val Lg6 = java.lang.Double.longBitsToDouble(0x3fc39a09d078c69fL) // 1.531383769920937332e-01
    private val Lg7 = java.lang.Double.longBitsToDouble(0x3fc2f112df3e5244L) // 1.479819860511658591e-01

    @opaque @library
    def compute(xInit: Double): Double = {

      if xInit.isNaN then Double.NaN
      else

        var hxInit = __HI(xInit) // high word of x
        val lx = __LO(xInit) // low  word of x, unsigned

        if hxInit < 0x0010_0000 && (((hxInit & EXP_SIGNIF_BITS) | lx) == 0) then -TWO54 / 0.0
        else if hxInit < 0 then (xInit - xInit) / 0.0
        else
          val xInit2 = if hxInit < 0x0010_0000 then xInit * TWO54 else xInit
          val hxInit2 = if hxInit < 0x0010_0000 then __HI(xInit2) else hxInit

          if hxInit2 >= EXP_BITS then  xInit2 + xInit2
          else
            val kInit: Int = (if hxInit < 0x0010_0000 then -54 else 0) + ((hxInit2 >> 20) - 1023)
            val hx: Int = hxInit2 & 0x000f_ffff
            val i: Int = (hx + 0x9_5f64) & 0x10_0000
            val x: Double = __HI(xInit2, hx | (i ^ 0x3ff0_0000)) // normalize x or x/2

            val k: Int = kInit + (i >> 20)
            val f = x - 1.0

            if (0x000f_ffff & (2 + hx)) < 3 then // |f| < 2**-20
              if f == 0.0 then
                if k == 0 then 0.0
                else
                  val dk = k.toDouble
                  dk * ln2_hi + dk * ln2_lo

              else
                val R = f * f * (0.5 - 0.33333333333333333 * f)
                if k == 0 then f - R
                else
                  val dk = k.toDouble
                  dk * ln2_hi - ((R - dk * ln2_lo) - f)
            else
              val s = f / (2.0 + f)
              val dk = k.toDouble
              val z = s * s
              val j = 0x6b851 - hx
              val i2 = (hx - 0x6_147a) | j
              val w = z * z
              val t1 = w * (Lg2 + w * (Lg4 + w * Lg6))
              val t2 = z * (Lg1 + w * (Lg3 + w * (Lg5 + w * Lg7)))
              val R = t2 + t1

              if i2 > 0 then
                val hfsq = 0.5 * f * f
                if k == 0 then f - (hfsq - s * (hfsq + R))
                else dk * ln2_hi - ((hfsq - (s * (hfsq + R) + dk * ln2_lo)) - f)
              else if k == 0 then f - s * (f - R)
              else dk * ln2_hi - ((s * (f - R) - dk * ln2_lo) - f)
    }.ensuring( res =>
      (res.isNaN == (xInit.isNaN || xInit < 0))
      && (xInit.isZero == res.isNegInfinity)
      && ((xInit.isFinite && xInit == 1.0) == (res.isZero && res.isPositive))
      && ((!xInit.isNaN && xInit >= 1.0) == res.isPositive)
      && (res.isNegative == (xInit.isFinite && 0.0 <= xInit && xInit < 1.0))
      && ((!xInit.isNaN && xInit >= 0) ==> res <= xInit - 1)
      && (xInit.isPosInfinity == res.isPosInfinity)
    )
  }

  object Log10 {
    private val ivln10 = java.lang.Double.longBitsToDouble(0x3fdbcb7b1526e50eL) // 4.34294481903251816668e-01
    private val log10_2hi = java.lang.Double.longBitsToDouble(0x3fd34413509f6000L) // 3.01029995663611771306e-01;
    private val log10_2lo = java.lang.Double.longBitsToDouble(0x3d59fef311f12b36L) // 3.69423907715893078616e-13;

    @opaque @library
    def compute(x: Double): Double = {
      if x.isNaN then Double.NaN
      else
        val hx = __HI(x) // high word of x
        val lx = __LO(x) // low word of x
        if (hx < 0x0010_0000) && (((hx & EXP_SIGNIF_BITS) | lx) == 0) then -TWO54 / 0.0
        else if hx < 0 then (x - x) / 0.0
        else
          val k = if hx < 0x0010_0000 then -54 else 0
          val x2 = if hx < 0x0010_0000 then x * TWO54 else x
          val hx2 = if hx < 0x0010_0000 then __HI(x2) else hx

          if hx2 >= EXP_BITS then
            x2 + x2
          else
            val k2 = k + (hx2 >> 20) - 1023
            val i  = (k2  & SIGN_BIT) >>> 31
            val y = (k2 + i).toDouble
            (y * log10_2lo + ivln10 * Log.compute(__HI(x2, (hx2 & 0x000f_ffff) | ((0x3ff - i) << 20)))) + y * log10_2hi
    }.ensuring( res =>
      (res.isNaN == (x.isNaN || x < 0))
        && (x.isZero == res.isNegInfinity)
        && ((x == 1.0) ==> (res.isZero && res.isPositive))
        && ((x >= 1.0) == res.isPositive)
        && (res.isNegative ==> (x < 1.0))
        && ((x.isFinite && x >= 0) ==> res < x)
        && (x.isPosInfinity == res.isPosInfinity)
    )
  }

  object Exp {
    private val half: Array[Double] = Array(0.5, -0.5)
    private val half0: Double = 0.5
    private val half1: Double = -0.5
    private val huge: Double = 1.0e+300
    private val twom1000: Double = java.lang.Double.longBitsToDouble(0x170000000000000L)
    private val o_threshold: Double = java.lang.Double.longBitsToDouble(0x40862e42fefa39efL)
    private val u_threshold: Double = java.lang.Double.longBitsToDouble(0xc0874910d52d3051L)
    private val ln2HI = Array(java.lang.Double.longBitsToDouble(0x3fe62e42fee00000L), java.lang.Double.longBitsToDouble(0xbfe62e42fee00000L))
    private val ln2HI0: Double = java.lang.Double.longBitsToDouble(0x3fe62e42fee00000L)
    private val ln2HI1: Double = java.lang.Double.longBitsToDouble(0xbfe62e42fee00000L)
    private val ln2LO = Array(java.lang.Double.longBitsToDouble(0x3dea39ef35793c76L), java.lang.Double.longBitsToDouble(0xbdea39ef35793c76L))
    private val ln2LO0 = java.lang.Double.longBitsToDouble(0x3dea39ef35793c76L)
    private val ln2LO1 = java.lang.Double.longBitsToDouble(0xbdea39ef35793c76L)

    private val invln2 = java.lang.Double.longBitsToDouble(0x3ff71547652b82feL)
    private val P1 = java.lang.Double.longBitsToDouble(0x3fc555555555553eL)
    private val P2 = java.lang.Double.longBitsToDouble(0xbf66c16c16bebd93L)
    private val P3 = java.lang.Double.longBitsToDouble(0x3f11566aaf25de2cL)
    private val P4 = java.lang.Double.longBitsToDouble(0xbebbbd41c5d26bf1L)
    private val P5 = java.lang.Double.longBitsToDouble(0x3e66376972bea4d0L)

    @library
    private def computeWithArrays(x: Double): Double = {

      if x.isNaN then Double.NaN else

        val hx: Int = __HI(x) /* high word of x */
        val xsb: Int = (hx >> 31) & 1 /* sign bit of x */
        val hx2: Int = hx & EXP_SIGNIF_BITS /* high word of |x| */

        /* filter out non-finite argument */
        if hx2 >= 0x40862E42 && (hx2 >= 0x7ff00000 || x > o_threshold || x < u_threshold) then
          /* if |x| >= 709.78... */
          if hx2 >= 0x7ff00000 then
            if ((hx2 & 0xfffff) | __LO(x)) != 0 then x + x /* NaN */
            else if xsb == 0 then x else 0.0 /* exp(+-inf) = {inf, 0} */
          else if (x > o_threshold) huge * huge /* overflow */
          else twom1000 * twom1000 /* underflow */
        else

          if !(hx2 > 0x3fd62e42) && hx2 < 0x3e300000 && huge + x > 1.0 then 1.0 + x
          else
            val k: Int = if hx2 > 0x3fd62e42 then if hx2 < 0x3FF0A2B2 then 1 - xsb - xsb else (invln2 * x + half(xsb)).toInt else 0
            val hi: Double = if hx2 > 0x3fd62e42 then if hx2 < 0x3FF0A2B2 then x - ln2HI(xsb) else x - k * ln2HI(0) else 0.0
            val lo: Double = if hx2 > 0x3fd62e42 then if hx2 < 0x3FF0A2B2 then ln2LO(xsb) else k * ln2LO(0) else 0.0
            val newX: Double = if hx2 > 0x3fd62e42 then hi - lo else x

            /* x is now in primary range */
            val t: Double = newX * newX
            val c: Double = newX - t * (P1 + t * (P2 + t * (P3 + t * (P4 + t * P5))))
            if k == 0 then 1.0 - ((newX * c) / (c - 2.0) - newX)
            else
              val y: Double = 1.0 - ((lo - (newX * c) / (2.0 - c)) - hi)
              if k >= -1021 then __HI(y, __HI(y) + (k << 20)) /* add k to y's exponent */
              else __HI(y, __HI(y) + ((k + 1000) << 20)) * twom1000
    }.ensuring( res => res.equiv(compute(x)))

    @opaque @library
    def compute(x: Double): Double = {

      if x.isNaN then Double.NaN else
        val hx: Int = __HI(x)
        /* high word of x */
        val xsb: Int = (hx >> 31) & 1
        /* sign bit of x */
        val hx2: Int = hx & EXP_SIGNIF_BITS /* high word of |x| */

        /* filter out non-finite argument */
        if hx2 >= 0x40862E42 && (hx2 >= 0x7ff00000 || x > o_threshold || x < u_threshold) then
          /* if |x| >= 709.78... */
          if hx2 >= 0x7ff00000 then
            if ((hx2 & 0xfffff) | __LO(x)) != 0 then x + x /* NaN */
            else if xsb == 0 then x else 0.0 /* exp(+-inf) = {inf, 0} */
          else if (x > o_threshold) huge * huge /* overflow */
          else twom1000 * twom1000 /* underflow */
        else if !(hx2 > 0x3fd62e42) && hx2 < 0x3e300000 && huge + x > 1.0 then 1.0 + x
        else
          val halfXsb = if xsb == 0 then half0 else half1
          val ln2HIXsb = if xsb == 0 then ln2HI0 else ln2HI1
          val ln2LOXsb = if xsb == 0 then ln2LO0 else ln2LO1
          val k: Int = if hx2 > 0x3fd62e42 then if hx2 < 0x3FF0A2B2 then 1 - xsb - xsb else (invln2 * x + halfXsb).toInt else 0
          val hi: Double = if hx2 > 0x3fd62e42 then if hx2 < 0x3FF0A2B2 then x - ln2HIXsb else x - k * ln2HI0 else 0.0
          val lo: Double = if hx2 > 0x3fd62e42 then if hx2 < 0x3FF0A2B2 then ln2LOXsb else k * ln2LO0 else 0.0
          val newX: Double = if hx2 > 0x3fd62e42 then hi - lo else x

          /* x is now in primary range */
          val t: Double = newX * newX
          val c: Double = newX - t * (P1 + t * (P2 + t * (P3 + t * (P4 + t * P5))))
          if k == 0 then 1.0 - ((newX * c) / (c - 2.0) - newX)
          else
            val y: Double = 1.0 - ((lo - (newX * c) / (2.0 - c)) - hi)
            if k >= -1021 then __HI(y, __HI(y) + (k << 20)) /* add k to y's exponent */
            else __HI(y, __HI(y) + ((k + 1000) << 20)) * twom1000
    }.ensuring(res =>
      res.isNaN == x.isNaN
      && (x.isPosInfinity ==> res.isPosInfinity)
      && (x.isNegInfinity ==> (res.isZero && res.isPositive))
      && (x.isZero ==> (res == 1))
      && ((!x.isNaN && x.isPositive) ==> res >= 1) // Converse does not hold: x = -7.458340731200206E-155
      && ((!x.isNaN && x.isNegative) ==> (0 <= res && res <= 1))
    )
  }

  object Expm1 {
    private val huge: Double = 1.0e+300
    private val tiny: Double = 1.0e-300
    private val o_threshold: Double = java.lang.Double.longBitsToDouble(0x40862e42fefa39efL)
    private val u_threshold: Double = java.lang.Double.longBitsToDouble(0xc0874910d52d3051L)
    private val ln2_hi: Double = java.lang.Double.longBitsToDouble(0x3fe62e42fee00000L)
    private val ln2_lo = java.lang.Double.longBitsToDouble(0x3dea39ef35793c76L)
    private val invln2 = java.lang.Double.longBitsToDouble(0x3ff71547652b82feL)

    private val Q1 = java.lang.Double.longBitsToDouble(0xbfa11111111110f4L)
    private val Q2 = java.lang.Double.longBitsToDouble(0x3f5a01a019fe5585L)
    private val Q3 = java.lang.Double.longBitsToDouble(0xbf14ce199eaadbb7L)
    private val Q4 = java.lang.Double.longBitsToDouble(0x3ed0cfca86e65239L)
    private val Q5 = java.lang.Double.longBitsToDouble(0xbe8afdb76e09c32dL)

    @opaque @library
    def compute(x: Double): Double = {
      if x.isNaN then Double.NaN else
        val hx = __HI(x) // high word of x
        val xsb = hx & SIGN_BIT // sign bit of x
        val y = stainless.math.abs(x)
        val hx2: Int = hx & EXP_SIGNIF_BITS /* high word of |x| */


        /* filter out non-finite argument */
        if hx2 >= 0x4043_687A && ((hx >= 0x4086_2E42 && (hx2 >= 0x7ff00000 || x > o_threshold)) || (xsb != 0 && x + tiny < 0.0)) then
          if hx >= 0x4086_2E42 then
            /* if |x| >= 709.78... */
            if hx2 >= 0x7ff00000 then
              if ((hx2 & 0xfffff) | __LO(x)) != 0 then x + x /* NaN */
              else if xsb == 0 then x else -1.0 /* exp(+-inf) = {inf, 0} */
            else huge * huge /* overflow */
          else tiny - 1.0
        else
          if !(hx2 > 0x3fd6_2e42) && hx2 < 0x3c90_0000 then x - ((huge + x) - (huge + x))
          else
            // argument reduction
            val k: Int = if hx2 > 0x3fd6_2e42 then if hx2 < 0x3FF0_A2B2 then if xsb == 0 then 1 else -1 else (invln2 * x + (if xsb == 0 then 0.5 else -0.5)).toInt else 0
            val hi: Double = if hx2 > 0x3fd6_2e42 then if hx2 < 0x3FF0_A2B2 then if xsb == 0 then x - ln2_hi else x + ln2_hi else x - k * ln2_hi else 0.0
            val lo: Double = if hx2 > 0x3fd6_2e42 then if hx2 < 0x3FF0_A2B2 then if xsb == 0 then ln2_lo else -ln2_lo else k * ln2_lo else 0.0
            val x2: Double = if hx2 > 0x3fd6_2e42 then hi - lo else x
            val c: Double = if hx2 > 0x3fd6_2e42 then (hi - x2) - lo else 0

            // x is now in primary range
            val hfx = 0.5 * x2
            val hxs = x2 * hfx
            val r1 = 1.0 + hxs * (Q1 + hxs * (Q2 + hxs * (Q3 + hxs * (Q4 + hxs * Q5))))
            val t = 3.0 - r1 * hfx
            val eInit = hxs * ((r1 - t) / (6.0 - x2 * t))
            if k == 0 then
              x2 - (x2 * eInit - hxs) // c is 0
            else
              val e = (x2 * (eInit - c) - c) - hxs
              if k == -1 then 0.5 * (x2 - e) - 0.5
              else if k == 1 then
                if x2 < -0.25 then -2.0 * (e - (x2 + 0.5)) else 1.0 + 2.0 * (x2 - e)
              else if k <= -2 || k > 56 then // suffice to return exp(x) - 1
                val y = 1.0 - (e - x2)
                __HI(y, __HI(y) + (k << 20)) - 1.0 // add k to y's exponent
              else
                if k < 20 then
                  val t = __HI(1.0, 0x3ff0_0000 - (0x2_00000 >> k)) // t = 1-2^-k
                  val y = t - (e - x2)
                  __HI(y, __HI(y) + (k << 20)) // add k to y's exponent
                else
                  val t = __HI(1.0, ((0x3ff - k) << 20)) // 2^-k
                  val y = (x2 - (e + t)) + 1
                  __HI(y, __HI(y) + (k << 20)) // add k to y's exponent


    }.ensuring(res =>
      res.isNaN == x.isNaN
        && (x.isPosInfinity ==> res.isPosInfinity)
        && (x.isNegInfinity ==> (res == -1))
        && (x.isZero ==> (res == 0))
        && ((!x.isNaN && x.isPositive) ==> res >= 0)
        && ((!x.isNaN && x.isNegative) ==> (-1 <= res && res <= 0))
    )
  }

  object Log1p {
    private val ln2_hi = java.lang.Double.longBitsToDouble(0x3fe62e42fee00000L) // 6.93147180369123816490e-01
    private val ln2_lo = java.lang.Double.longBitsToDouble(0x3dea39ef35793c76L) // 1.90821492927058770002e-10
    private val Lp1 = java.lang.Double.longBitsToDouble(0x3fe5555555555593L) // 6.666666666666735130e-01
    private val Lp2 = java.lang.Double.longBitsToDouble(0x3fd999999997fa04L) // 3.999999999940941908e-01
    private val Lp3 = java.lang.Double.longBitsToDouble(0x3fd2492494229359L) // 2.857142874366239149e-01
    private val Lp4 = java.lang.Double.longBitsToDouble(0x3fcc71c51d8e78afL) // 2.222219843214978396e-01
    private val Lp5 = java.lang.Double.longBitsToDouble(0x3fc7466496cb03deL) // 1.818357216161805012e-01
    private val Lp6 = java.lang.Double.longBitsToDouble(0x3fc39a09d078c69fL) // 1.531383769920937332e-01
    private val Lp7 = java.lang.Double.longBitsToDouble(0x3fc2f112df3e5244L) // 1.479819860511658591e-01

    @opaque @library
    def compute(x: Double): Double = {
      if x.isNaN then Double.NaN
      else
        val hx: Int = __HI(x) /* high word of x */
        val ax: Int = hx & EXP_SIGNIF_BITS
        if hx < 0x3FDA_827A && (ax >= 0x3ff0_0000 || ax < 0x3e20_0000) then
          /* x < 0.41422  */
          if ax >= 0x3ff0_0000 then
            /* x <= -1.0 */
            if x == -1.0 /* log1p(-1)=-inf */ then Double.NegativeInfinity
            else  Double.NaN /* log1p(x < -1) = NaN */
          else
            /* |x| < 2**-29 */
            if TWO54 + x > 0.0 /* raise inexact */ && ax < 0x3c90_0000 /* |x| < 2**-54 */ then x
            else  x - x * x * 0.5
        else
          val k: Int = if hx < 0x3FDA_827A && (hx > 0 || hx <= 0xbfd2_bec3) then 0 else 1
          val f: Double = if hx < 0x3FDA_827A && (hx > 0 || hx <= 0xbfd2_bec3) then x else 0.0
          val huInit: Int = if hx < 0x3FDA_827A && (hx > 0 || hx <= 0xbfd2_bec3) then 1 else 0

          if hx >= EXP_BITS then x + x
          else
            val u: Double = if k != 0 then if hx < 0x4340_0000 then 1.0 + x else x else 0.0
            val hu: Int = if k != 0 then __HI(u) else 0
            val k2: Int = if k != 0 then (hu >> 20) - 1023 else k
            val c: Double = if k != 0 then if hx < 0x4340_0000 then (if k2 > 0 then 1.0 - (u - x) else x - (u - 1.0)) / u else 0 else 0.0
            val hu2: Int = if k != 0 then hu & 0x000f_ffff else hu
            val k3 = if (k != 0) && !(hu2 < 0x6_a09e) then k2 + 1 else k2
            val u2 = if k != 0 then if hu2 < 0x6_a09e then __HI(u, hu2 | 0x3ff0_0000) else __HI(u, hu2 | 0x3fe0_0000) else u
            val f2 = if k != 0 then u2 - 1.0 else f

            val hfsq = 0.5 * f2 * f2
            if hu2 == 0 then
              /* |f| < 2**-20 */
              if f2 == 0.0 then
                if k3 == 0 then 0.0
                else k3 * ln2_hi + (c + k3 * ln2_lo)
              else
                val R = hfsq * (1.0 - 0.66666666666666666 * f2)
                if k3 == 0 then f2 - R
                else k3 * ln2_hi - ((R - (k3 * ln2_lo + c)) - f2)
            else
              val s = f2 / (2.0 + f2)
              val z = s * s
              val R = z * (Lp1 + z * (Lp2 + z * (Lp3 + z * (Lp4 + z * (Lp5 + z * (Lp6 + z * Lp7))))))

              if k3 == 0 then f2 - (hfsq - s * (hfsq + R))
              else k3 * ln2_hi - ((hfsq - (s * (hfsq + R) + (k3 * ln2_lo + c))) - f2)
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
  }

  object Sinh {
    private val shuge = 1.0e307

    @opaque @library
    def compute(x: Double): Double = {

      if x.isNaN then Double.NaN else
        // High word of |x|
        val jx = __HI(x)
        val ix = jx & EXP_SIGNIF_BITS
        // x is INF or NaN
        if ix >= EXP_BITS then x + x
        else
          val h = if jx < 0 then -0.5 else 0.5

          // |x| in [0,22], return sign(x)*0.5*(E+E/(E+1)))
          if ix < 0x4036_0000 then // |x| < 22
            if (ix < 0x3e30_0000) && (shuge + x > 1.0) then x // sinh(tiny) = tiny with inexact // |x| < 2**-28
            else
              val t = Exp.compute(stainless.math.abs(x))
              unfold(Exp.compute(stainless.math.abs(x)))
              if ix < 0x3ff0_0000 then
                h * (2.0 * t - t * t / (t + 1.0))
              else
                h * (t + t / (t + 1.0))
              else
            // |x| in [22, log(maxdouble)] return 0.5*exp(|x|)
            if ix < 0x4086_2E42 then h * Exp.compute(stainless.math.abs(x))
            else
              // |x| in [log(maxdouble), overflowthreshold]
              val lx = __LO(x)
              if ix < 0x4086_33CE || ((ix == 0x4086_33ce) && (LongHelpers.compareUnsigned(lx, 0x8fb9_f87d) <= 0)) then
                val w = Exp.compute(0.5 * stainless.math.abs(x))
                val t = h * w
                t * w
              else x * shuge // |x| > overflowthreshold, sinh(x) overflow
    }.ensuring(res =>
      res.isNaN == x.isNaN
        && (x.isPosInfinity ==> res.isPosInfinity)
        && (x.isNegInfinity ==> res.isNegInfinity)
        && (x.isZero ==> res.isZero)
        && (x.isPositive == res.isPositive)
        && (x.isNegative == res.isNegative)
    )
  }

  object Cosh {
    private val huge = 1.0e300
    @opaque @library
    def compute(x: Double): Double = {
      if x.isNaN then Double.NaN
      else
        // High word of |x|
        val ix = __HI(x) & EXP_SIGNIF_BITS
        // x is INF or NaN
        if ix >= EXP_BITS then x * x
        else
          // |x| in [0,0.5*ln2], return 1+expm1(|x|)^2/(2*exp(|x|))
          if ix < 0x3fd6_2e43 then
            unfold(Expm1.compute(stainless.math.abs(x)))
            val t = Expm1.compute(stainless.math.abs(x))
            val w = 1.0 + t
            if ix < 0x3c80_0000 then w // cosh(tiny) = 1
            else 1.0 + (t * t) / (w + w)
          else
            // |x| in [0.5*ln2, 22], return (exp(|x|) + 1/exp(|x|)/2
            if ix < 0x4036_0000 then
              val t = Exp.compute(stainless.math.abs(x))
              unfold(Exp.compute(stainless.math.abs(x)))
              0.5 * t + 0.5 / t
            else
              // |x| in [22, log(maxdouble)] return 0.5*exp(|x|)
              if ix < 0x4086_2E42 then {
                unfold(Exp.compute(stainless.math.abs(x)))
                0.5 * Exp.compute(stainless.math.abs(x))
              } else
                // |x| in [log(maxdouble), overflowthreshold]
                val lx = __LO(x)
                if ix < 0x4086_33CE || ((ix == 0x4086_33ce) && (IntHelpers.compareUnsigned(lx, 0x8fb9_f87d) <= 0)) then
                  val w = Exp.compute(0.5 * stainless.math.abs(x))
                  unfold(Exp.compute(0.5 * stainless.math.abs(x)))
                  val t = 0.5 * w
                  t * w
                else
                  // |x| > overflowthreshold, cosh(x) overflow
                  huge * huge
    }.ensuring(res =>
      res.isNaN == x.isNaN
//        && (!x.isNaN ==> (res >= 1))
        && (!x.isNaN ==> res.isPositive)
        && (x.isInfinity ==> res.isPosInfinity)
        && (x.isZero ==> (res == 1.0))
    )
  }

  object Tanh {
    private val tiny = 1.0e-300

    @opaque @library
    def compute(x: Double): Double = {
      if x.isNaN then Double.NaN
      else
        // High word of |x|.
        val jx = __HI(x)
        val ix = jx & EXP_SIGNIF_BITS
        // x is INF or NaN
        if ix >= EXP_BITS then
          if jx >= 0 then // tanh(+-inf)=+-1
            1.0 / x + 1.0
          else  // tanh(NaN) = NaN
            1.0 / x - 1.0
        else
          // |x| < 22
          if ix < 0x4036_0000 && ix < 0x3c80_0000 then x * (1.0 + x) // tanh(small) = small // |x| < 2**-55
          else
            val z =
              if ix < 0x4036_0000 then
                if ix >= 0x3ff0_0000 then // |x| >= 1
                  1.0 - 2.0 / (Expm1.compute(2.0 * stainless.math.abs(x)) + 2.0)
                else
                  val t = Expm1.compute(-2.0 * stainless.math.abs(x))
                  -t / (t + 2.0)
              else // |x| > 22, return +-1
                1.0 - tiny // raised inexact flag
            if jx >= 0 then z else -z
    }.ensuring(res =>
      (x.isNaN == x.isNaN)
      && (!x.isNaN ==> (-1 <= res && res <= 1))
      && (x.isPositive ==> res >= 0)
      && (x.isNegative ==> res <= 0)
      && (x.isNegInfinity ==> (res == -1))
      && (x.isPosInfinity ==> (res == 1))
      && (x.isZero ==> res.isZero)
    )
  }
}
