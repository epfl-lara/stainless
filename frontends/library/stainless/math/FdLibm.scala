package stainless
package math

import stainless.annotation.*
import stainless.lang.*

private object LongHelpers {
  @library
  def compare(x: Long, y: Long): Int = if x < y then -1 else if x == y then 0 else 1

  @library
  def compareUnsigned(x: Long, y: Long): Int = math.wrapping(compare(x + Long.MinValue, y + Long.MinValue))
}

private object IntHelpers {
  @library
  def compare(x: Int, y: Int): Int = if x < y then -1 else if x == y then 0 else 1

  @library
  def compareUnsigned(x: Int, y: Int): Int = math.wrapping(compare(x + Int.MinValue, y + Int.MinValue))
}

// The FdLibm object is annotated with @extern to avoid running the verification in CI.
// A full verification run of the FdLibm object will typically take multiple hours.
// The flag `--strict-arithmetic=false` should be disabled for verification to succeed.
// The verification has only been tested with `--solvers=smt-z3,smt-cvc5,smt-bitwuzla`.
// Using `--solver:cvc5=--arrays-exp` improves performance significantly; Inox currently (2026-01-21) generates
// array constraints that require experimental array features to be enabled in cvc5,
// even though these features are disabled by default.
@extern
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
  private def __LO_CHECKED(x: Double): Int = {
    require(!x.isNaN)
    __LO(x)
  }

  @library
  private def __LO(x: Double): Int = {
    val transducer = java.lang.Double.doubleToLongBits(x)
    stainless.math.wrapping(transducer.toInt)
  }

  /**
   * Return a double with its low-order bits of the second argument
   * and the high-order bits of the first argument.
   */
  @library
  private def __LO_CHECKED(x: Double, low: Int): Double = {
    require(!x.isNaN)
    __LO(x, low)
  }//.ensuring(res => (x.isFinite == res.isFinite) && (x.isFinite ==> (x.isPositive == res.isPositive)) && (x.isFinite ==> (x.isNegative == res.isNegative)))


  @library
  private def __LO(x: Double, low: Int): Double = {
    val transX = java.lang.Double.doubleToLongBits(x)
    java.lang.Double.longBitsToDouble((transX & 0xFFFF_FFFF_0000_0000L) | (low & 0x0000_0000_FFFF_FFFFL))
  }//.ensuring(res => (x.isFinite == res.isFinite) && (x.isFinite ==> (x.isPositive == res.isPositive)) && (x.isFinite ==> (x.isNegative == res.isNegative)))

  /**
   * Return the high-order 32 bits of the double argument as an int.
   */
  @library
  private def __HI_CHECKED(x: Double): Int = {
    require(!x.isNaN)
    __HI(x)
  }

  @library
  private def __HI(x: Double): Int = {
    val transducer = java.lang.Double.doubleToLongBits(x)
    (transducer >> 32).toInt
  }

  /**
   * Return a double with its high-order bits of the second argument
   * and the low-order bits of the first argument..
   */
  @library
  private def __HI_CHECKED(x: Double, high: Int): Double = {
    require(!x.isNaN)
    __HI(x, high)
  }

  @library
  private def __HI(x: Double, high: Int): Double = {
    val transX = java.lang.Double.doubleToLongBits(x)
    java.lang.Double.longBitsToDouble((transX & 0x0000_0000_FFFF_FFFFL) | high.toLong << 32)
  }

  @library
  private def __HI_LO(high: Int, low: Int): Double = {
    java.lang.Double.longBitsToDouble((high.toLong << 32) | (low & 0xffff_ffffL))
  }

  @library
  object Sin {
    @opaque
    def compute(x: Double): Double = {
      val ix = __HI(x) & EXP_SIGNIF_BITS
      if (ix <= 0x3fe9_21fb) // |x| ~< pi / 4
        unfold(__kernel_sin(x, 0.0d, 0))
        __kernel_sin(x, 0.0d, 0)
      else if (ix >= EXP_BITS) // sin(Inf or NaN) is NaN
        x - x
      else {
        val (n, y0, y1) = RemPio2.__ieee754_rem_pio2(x)
        n & 3 match {
          case 0 => Sin.__kernel_sin(y0, y1, 1)
          case 1 => Cos.__kernel_cos(y0, y1)
          case 2 => -Sin.__kernel_sin(y0, y1, 1)
          case _ => -Cos.__kernel_cos(y0, y1)
        }
      }
    }.ensuring(res =>
      (!x.isFinite == res.isNaN)
        && (x.equiv(+0.0d) ==> res.equiv(+0.0d))
        && (x.equiv(-0.0d) ==> res.equiv(-0.0d))
        && (res.isNaN || -1.0d <= res && res <= 1.0d)
    )

    private val S1 = -1.66666666666666324348e-01d // -0x1.5555555555549p-3
    private val S2 = 8.33333333332248946124e-03d // 0x1.111111110f8a6p-7
    private val S3 = -1.98412698298579493134e-04d // -0x1.a01a019c161d5p-13
    private val S4 = 2.75573137070700676789e-06d // 0x1.71de357b1fe7dp-19
    private val S5 = -2.50507602534068634195e-08d // -0x1.ae5e68a2b9cebp-26
    private val S6 = 1.58969099521155010221e-10d // 0x1.5d93a5acfd57cp-33

    @opaque
    private[FdLibm] def __kernel_sin(x: Double, y: Double, iy: Int): Double = {
      require(x.isFinite && -0.7854 <= x && x <= 0.7854)
      require(y.isFinite && -1.1102230246251565E-16 <= y && y <= 1.1102230246251565E-16)
      val ix = __HI(x) & EXP_SIGNIF_BITS
      if (ix < 0x3e40_0000) { // abs(x) < 7.450580596923828125e-9
        if (x.toInt == 0)
          return x
      }

      val z = x * x
      val v = z * x
      val r = S2 + z * (S3 + z * (S4 + z * (S5 + z * S6)))

      if (iy == 0)
        x + v * (S1 + z * r)
      else
        x - ((z * (0.5d * y - v * r) - y) - v * S1)
    }.ensuring(res => -1.0d <= res && res <= 1.0d) // very loose bounds
  }

  @library
  object Cos {
    @opaque
    def compute(x: Double): Double = {
      val ix = __HI(x) & EXP_SIGNIF_BITS
      if (ix <= 0x3fe9_21fb) // |x| ~< pi / 4
        __kernel_cos(x, 0.0d)
      else if (ix >= EXP_BITS) // sin(Inf or NaN) is NaN
        x - x
      else {
        val (n, y0, y1) = RemPio2.__ieee754_rem_pio2(x)
        n & 3 match {
          case 0 => Cos.__kernel_cos(y0, y1)
          case 1 => -Sin.__kernel_sin(y0, y1, 1)
          case 2 => -Cos.__kernel_cos(y0, y1)
          case _ => Sin.__kernel_sin(y0, y1, 1)
        }
      }
    }.ensuring(res =>
      (!x.isFinite == res.isNaN)
        && (res.isNaN || -1.0d <= res && res <= 1.0d)
    )

    private val C1 = 4.16666666666666019037e-02d //  0x1.555555555554cp-5
    private val C2 = -1.38888888888741095749e-03d // -0x1.6c16c16c15177p-10
    private val C3 = 2.48015872894767294178e-05d //  0x1.a01a019cb159p-16
    private val C4 = -2.75573143513906633035e-07d // -0x1.27e4f809c52adp-22
    private val C5 = 2.08757232129817482790e-09d //  0x1.1ee9ebdb4b1c4p-29
    private val C6 = -1.13596475577881948265e-11d // -0x1.8fae9be8838d4p-37

    @opaque
    private[FdLibm] def __kernel_cos(x: Double, y: Double): Double = {
      require(x.isFinite && -0.7854 <= x && x <= 0.7854)
      require(y.isFinite && -1.1102230246251565E-16 <= y && y <= 1.1102230246251565E-16)
      val ix = __HI(x) & EXP_SIGNIF_BITS
      if (ix < 0x3e40_0000) { // abs(x) < 7.450580596923828125e-9
        if (x.toInt == 0)
          return 1.0d
      }

      val z = x * x
      val r = z * (C1 + z * (C2 + z * (C3 + z * (C4 + z * (C5 + z * C6)))))

      if (ix < 0x3FD3_3333) // |x| < 0.3
        1.0 - (0.5 * z - (z * r - x * y))
      else {
        val qx = if (ix > 0x3fe9_0000) // x > 0.78125
          0.28125d
        else
          __HI_LO(ix - 0x0020_0000, 0)
        val hz = 0.5d * z - qx
        val a = 1.0d - qx
        a - (hz - (z * r - x * y))
      }
    }.ensuring(res => -1.0d <= res && res <= 1.0d) // very loose bounds
  }

  @library
  object Tan {
    @opaque
    def compute(x: Double): Double = {
      var n = 0
      var ix = 0
      // High word of x.
      ix = __HI(x)
      // |x| ~< pi/4
      ix &= EXP_SIGNIF_BITS
      if (ix <= 0x3fe9_21fb) __kernel_tan(x, 0d, 1)
      else if (ix >= EXP_BITS) { // tan(Inf or NaN) is NaN
        x - x // NaN
      }
      else { // argument reduction needed
        val (n, y0, y1) = RemPio2.__ieee754_rem_pio2(x)
        __kernel_tan(y0, y1, 1 - ((n & 1) << 1)) // 1 -- n even; -1 -- n odd
      }
    }.ensuring(res =>
      ((x.isNaN || x.isInfinity) ==> res.isNaN)
        && ((x.isPositive && x.isZero) ==> (res.isPositive && res.isZero))
        && ((x.isNegative && x.isZero) ==> (res.isNegative && res.isZero))
    )

    private val pio4 = 7.85398163397448278999e-01   // 0x1.921fb54442d18p-1
    private val pio4lo = 3.06161699786838301793e-17 // 0x1.1a62633145c07p-55

    private val T0 = 3.33333333333334091986e-01   // 0x1.5555555555563p-2
    private val T1 = 1.33333333333201242699e-01   // 0x1.111111110fe7ap-3
    private val T2 = 5.39682539762260521377e-02   // 0x1.ba1ba1bb341fep-5
    private val T3 = 2.18694882948595424599e-02   // 0x1.664f48406d637p-6
    private val T4 = 8.86323982359930005737e-03   // 0x1.226e3e96e8493p-7
    private val T5 = 3.59207910759131235356e-03   // 0x1.d6d22c9560328p-9
    private val T6 = 1.45620945432529025516e-03   // 0x1.7dbc8fee08315p-10
    private val T7 = 5.88041240820264096874e-04   // 0x1.344d8f2f26501p-11
    private val T8 = 2.46463134818469906812e-04   // 0x1.026f71a8d1068p-12
    private val T9 = 7.81794442939557092300e-05   // 0x1.47e88a03792a6p-14
    private val T10 = 7.14072491382608190305e-05  // 0x1.2b80f32f0a7e9p-14
    private val T11 = -1.85586374855275456654e-05 // -0x1.375cbdb605373p-16
    private val T12 = 2.59073051863633712884e-05  // 0x1.b2a7074bf7ad4p-16

    @opaque
    private def __kernel_tan(x: Double, y: Double, iy: Int): Double = {
      require(x.isFinite && -0.7854 <= x && x <= 0.7854)
      require(y.isFinite && -1.1102230246251565E-16 <= y && y <= 1.1102230246251565E-16)

      val hx = __HI(x) // high word of x
      val ix = hx & EXP_SIGNIF_BITS // high word of |x|

      if (ix < 0x3e30_0000 && x.toInt == 0) { // x < 2**-28 // generate inexact
        if (math.wrapping((ix | __LO(x)) | (iy + 1)) == 0) 1.0 / math.abs(x)
        else if (iy == 1) x
        else { // compute -1 / (x+y) carefully
          val w = x + y
          val z = __LO(w, 0)
          val v = y - (z - x)
          val a = -1.0 / w
          val t = __LO(a, 0)
          val s = 1.0 + t * z
          t + a * (s + t * v)
        }
      }
      else {
        val (x1, y1) = if (ix < 0x3FE5_9428) {
          (x, y)
        } else { // |x| >= 0.6744
          val x1 = if hx < 0 then -x else x
          val y1 = if hx < 0 then -y else y
          val z = pio4 - x1
          val w = pio4lo - y1
          (z + w, 0d)
        }
        val z = x1 * x1
        val w1 = z * z
        val r1 = T1 + w1 * (T3 + w1 * (T5 + w1 * (T7 + w1 * (T9 + w1 * T11))))
        val v = z * (T2 + w1 * (T4 + w1 * (T6 + w1 * (T8 + w1 * (T10 + w1 * T12)))))
        val s = z * x1
        val r2 = (y1 + z * (s * (r1 + v) + y1)) + T0 * s
        val w2 = x1 + r2
        if (ix >= 0x3FE5_9428) {
          val v = iy.toDouble
          (1 - ((hx >> 30) & 2)).toDouble * (v - 2.0d * (x1 - (w2 * w2 / (w2 + v) - r2)))
        }
        else if (iy == 1) w2
        else {
          val z = __LO(w2, 0)
          val v = r2 - (z - x1)
          val a = -1.0 / w2
          val t = __LO(a, 0)
          val s = 1.0 + t * z
          t + a * (s + t * v)
        }
      }
    }.ensuring(res =>
        ((x.isPositive && x.isZero && y.isZero && iy == 1) ==> (res.isPositive && res.isZero))
        && ((x.isNegative && x.isZero && y.isZero && iy == 1) ==> (res.isNegative && res.isZero))
    )
  }

  @library
  object RemPio2 {
    private val npio2_hw = Array[Int](
      0x3FF921FB, 0x400921FB, 0x4012D97C, 0x401921FB, 0x401F6A7A, 0x4022D97C,
      0x4025FDBB, 0x402921FB, 0x402C463A, 0x402F6A7A, 0x4031475C, 0x4032D97C,
      0x40346B9C, 0x4035FDBB, 0x40378FDB, 0x403921FB, 0x403AB41B, 0x403C463A,
      0x403DD85A, 0x403F6A7A, 0x40407E4C, 0x4041475C, 0x4042106C, 0x4042D97C,
      0x4043A28C, 0x40446B9C, 0x404534AC, 0x4045FDBB, 0x4046C6CB, 0x40478FDB,
      0x404858EB, 0x404921FB)

    private val invpio2 = 6.36619772367581382433e-01d // 0x1.45f306dc9c883p-1
    private val pio2_1 = 1.57079632673412561417e+00d // 0x1.921fb544p0
    private val pio2_1t = 6.07710050650619224932e-11d // 0x1.0b4611a626331p-34
    private val pio2_2 = 6.07710050630396597660e-11d // 0x1.0b4611a6p-34
    private val pio2_2t = 2.02226624879595063154e-21d // 0x1.3198a2e037073p-69
    private val pio2_3 = 2.02226624871116645580e-21d // 0x1.3198a2ep-69
    private val pio2_3t = 8.47842766036889956997e-32d // 0x1.b839a252049c1p-104

    @opaque
    def __ieee754_rem_pio2(x: Double): (Int, Double, Double) = {
      val hx = __HI(x)
      val ix = hx & EXP_SIGNIF_BITS
      if (ix >= EXP_BITS) { // x is inf or NaN
        assert(!x.isFinite)
        (0, x - x, x - x)
      }
      else if (ix <= 0x3fe9_21fb) { // |x| ~<= pi/4 , no need for reduction
        assert(-0.785398483276367076478d <= x && x <= 0.785398483276367076478d)
        (0, x, 0d)
      }
      else if (ix < 0x4002_d97c) { // |x| < 3pi/4, special case with n=+-1
        assert(-2.35619354248046875d < x && x < -0.785398483276367076478d || 0.785398483276367076478d < x && x < 2.35619354248046875d)
        if (hx > 0) { // positive x
          if (ix != 0x3ff9_21fb) { // 33+53 bit pi is good enough
            val z = x - pio2_1
            (1, z - pio2_1t, (z - (z - pio2_1t)) - pio2_1t)
          } else { // near pi/2, use 33+33+53 bit pi
            val z = (x - pio2_1) - pio2_2
            (1, z - pio2_2t, (z - (z - pio2_2t)) - pio2_2t)
          }
        } else { // negative x
          if (ix != 0x3ff_921fb) { // 33+53 bit pi is good enough
            val z = x + pio2_1
            (-1, z + pio2_1t, (z - (z + pio2_1t)) + pio2_1t)
          } else { // near pi/2, use 33+33+53 bit pi
            val z = (x + pio2_1) + pio2_2
            (-1, z + pio2_2t, (z - (z + pio2_2t)) + pio2_2t)
          }
        }
      }
      // We skip this case for now since it seems like it is currently too challenging for SMT-solvers.
//      else if (ix <= 0x4139_21fb) { // |x| ~<= 2^19*(pi/2), medium size // TODO: should this not say 2^20??
//        assert(-1647099.99999999976717d <= x && x <= -2.35619354248046875d || 2.35619354248046875d <= x && x <= 1647099.99999999976717d)
//        val j = ix >> 20
//        val abs_x = math.abs(x)
//        val n = (abs_x * invpio2 + 0.5).toInt
//        val fn = n.toDouble
//        val r0 = abs_x - fn * pio2_1 // 1st round good to 85 bit
//        val w0 = fn * pio2_1t
//        val y0 = r0 - w0
//        val (yy0, yy1) = if (n < 32 && ix != npio2_hw(n - 1) || j - ((__HI(y0) >> 20) & 0x7ff) <= 16) {
//          (y0, (r0 - y0) - w0)
//        } else { // 2nd iteration needed, good to 118
//          val r1 = r0 - fn * pio2_2
//          val w1 = fn * pio2_2t - ((r0 - r1) - fn * pio2_2)
//          val y1 = r1 - w1
//          if (j - ((__HI(y1) >> 20) & 0x7ff) <= 49) {
//            (y1, (r1 - y1) - w1)
//          } else { // 3rd iteration need, 151 bits acc, will cover all possible cases
//            val r2 = r1 - fn * pio2_3
//            val w2 = fn * pio2_3t - ((r1 - r2) - fn * pio2_3)
//            val y2 = r2 - w2
//            (y2, (r2 - y2) - w2)
//          }
//        }
//        if hx < 0 then (-n, -yy0, -yy1) else (n, yy0, yy1)
//      }
      else { // all other (large) arguments
        assert(x <= -2.35619354248046875d || 2.35619354248046875d <= x)
        val (n1, y0, y1) = KernelRemPio2.__kernel_rem_pio2(math.abs(x))
        if hx < 0 then (-n1, -y0, -y1) else (n1, y0, y1)
      }
    }.ensuring(res =>
      (!x.isFinite ||
        ((-8 < res._1 && res._1 < 8)
          && -0.785398483276367076478d <= res._2 && res._2 <= 0.785398483276367076478d
          && -1.1102230246251565E-16 <= res._3 && res._3 <= 1.1102230246251565E-16))
    )
  }

  @library
  object KernelRemPio2 {
    // This object is based on the OpenJDK class `KernelRemPio2`, with modifications to simplify Stainless proofs.
    // Some of the main changes:
    // - the signature of `__kernel_rem_pio2()` has been changed
    //   - it now accepts doubles as inputs, not arrays of 24-bit chunks of numbers (here, we only care about doubles anyway)
    //   - the result is now computed with constant precision, not an argument-dependant precision
    // - the body of `__kernel_rem_pio2()` has been split into several methods to clarify the structure of the algorithm and to avoid stack overflows in Stainless
    // - the input splitting may pad the input with leading zeros to ensure that the exponent of `q(0)` is always zero
    // - the product of the input and two over pi is now evaluated using a constant precision, not an adaptive precision like in the original
    //   - but, adaptive precision can probably be added again as a performance optimization
    // - the compression of the result into a double-double is implemented in a different way to allow for a simple loop invariant
    // - some loops are partially unrolled to help the SMT-solvers
    // - new functions and constants for proof annotations have been added

    //// Constants ////

    private val two_over_pi = Array[Int]( // moved to this object from RemPio2
      0xA2F983, 0x6E4E44, 0x1529FC, 0x2757D1, 0xF534DD, 0xC0DB62,
      0x95993C, 0x439041, 0xFE5163, 0xABDEBB, 0xC561B7, 0x246E3A,
      0x424DD2, 0xE00649, 0x2EEA09, 0xD1921C, 0xFE1DEB, 0x1CB129,
      0xA73EE8, 0x8235F5, 0x2EBB44, 0x84E99C, 0x7026B4, 0x5F7E41,
      0x3991D6, 0x398353, 0x39F49C, 0x845F8B, 0xBDF928, 0x3B1FF8,
      0x97FFDE, 0x05980F, 0xEF2F11, 0x8B5A0A, 0x6D1F6D, 0x367ECF,
      0x27CB09, 0xB74F46, 0x3F669E, 0x5FEA2D, 0x7527BA, 0xC7EBE5,
      0xF17B3D, 0x0739F7, 0x8A5292, 0xEA6BFB, 0x5FB11F, 0x8D5D08,
      0x560330, 0x46FC7B, 0x6BABF0, 0xCFBC20, 0x9AF436, 0x1DA9E3,
      0x91615E, 0xE61B08, 0x659985, 0x5F14A0, 0x68408D, 0xFFD880,
      0x4D7327, 0x310606, 0x1556CA, 0x73A8C9, 0x60E27B, 0xC08C6B)

    private val PIo2 = Array[Double](
      1.57079625129699707031e+00d, // 0x1.921fb4p0,
      7.54978941586159635335e-08d, // 0x1.4442dp-24,
      5.39030252995776476554e-15d, // 0x1.846988p-48,
      3.28200341580791294123e-22d, // 0x1.8cc516p-72,
      1.27065575308067607349e-29d, // 0x1.01b838p-96,
      1.22933308981111328932e-36d, // 0x1.a25204p-120,
      2.73370053816464559624e-44d, // 0x1.382228p-145,
      2.16741683877804819444e-51d) // 0x1.9f31dp-169,

    private val twon24 = 5.96046447753906250000e-08d // 0x1.0p-24

    private val twon24Pow = Array[Double](
      1,
      5.9604644775390625E-8,
      3.552713678800501E-15,
      2.1175823681357508E-22,
      1.2621774483536189E-29,
      7.52316384526264E-37,
      4.4841550858394146E-44,
      2.6727647100921956E-51,
      1.5930919111324523E-58,
      9.495567745759799E-66,
      5.659799424266695E-73,
      3.3735033418337674E-80,
      2.0107646833859488E-87,
      1.1985091468012028E-94,
      7.143671195514219E-102,
      4.2579598400081507E-109,
      2.5379418373156492E-116,
      1.512731216738015E-123,
      9.016580681431383E-131,
      5.374300886053671E-138
    )

    //// Helpers for expressing invariants ////

    @pure
    private def all5(a: Array[Double], P: Double => Boolean): Boolean = {
      require(a.length == 5)
      P(a(0)) && P(a(1)) && P(a(2)) && P(a(3)) && P(a(4))
    }

    @pure
    private def all20(a: Array[Double], P: Double => Boolean): Boolean = {
      require(a.length == 20)
      P(a(0)) && P(a(1)) && P(a(2)) && P(a(3)) && P(a(4)) && P(a(5)) && P(a(6)) && P(a(7)) && P(a(8)) && P(a(9)) && P(a(10)) && P(a(11)) && P(a(12)) && P(a(13)) && P(a(14)) && P(a(15)) && P(a(16)) && P(a(17)) && P(a(18)) && P(a(19))
    }

    @pure
    private def all20Int(a: Array[Int], P: Int => Boolean): Boolean = {
      require(a.length == 20)
      P(a(0)) && P(a(1)) && P(a(2)) && P(a(3)) && P(a(4)) && P(a(5)) && P(a(6)) && P(a(7)) && P(a(8)) && P(a(9)) && P(a(10)) && P(a(11)) && P(a(12)) && P(a(13)) && P(a(14)) && P(a(15)) && P(a(16)) && P(a(17)) && P(a(18)) && P(a(19))
    }

    private def P(x: Double): Boolean = !x.isNaN && 0 <= x && x <= 5 * 0xffff_ffff_ffffL

    private def Q(x: Double): Boolean = !x.isNaN && 0 <= x && x <= 0xff_ffff

    private def QInt(x: Int): Boolean = 0 <= x && x <= 0xff_ffff

    //// Invariants and bound arrays ////

    @pure
    private def xxInv(xx: Array[Double]): Boolean = xx.length == 5 && all5(xx, Q)

    @pure
    private def fInv(f: Array[Double]): Boolean = f.length == 20 && all20(f, Q)

    @pure
    private def qInv(q: Array[Double]): Boolean = q.length == 20 && all20(q, P)

    @pure
    private def iqInv(iq: Array[Int]): Boolean = iq.length == 20 && all20Int(iq, QInt)

    private val qqBound = Array[Double](
      0.4999999403953552,
      5.9604641222676946E-8,
      3.552713467042264E-15,
      2.117582241918006E-22,
      1.2621773731219804E-29,
      7.5231633968471315E-37,
      4.4841548185629436E-44,
      2.6727645507830045E-51,
      1.5930918161767748E-58,
      9.495567179779856E-66,
      5.659799086916361E-73,
      3.373503140757299E-80,
      2.0107645635350341E-87,
      1.1985090753644908E-94,
      7.143670769718235E-102,
      4.257959586213967E-109,
      2.5379416860425275E-116,
      1.5127311265722081E-123,
      9.016580144001294E-131,
      5.374300565720376E-138,
    )

    @pure
    private def qqInv(qq: Array[Double]): Boolean = {
      qq.length == 20 && all20(qq, !_.isNaN)
        && 0 <= qq(0) && qq(0) <= 0.4999999403953552 // replacing this by `qqBound(0)` etc. seems to have a negative impact on solver performance
        && 0 <= qq(1) && qq(1) <= 5.9604641222676946E-8
        && 0 <= qq(2) && qq(2) <= 3.552713467042264E-15
        && 0 <= qq(3) && qq(3) <= 2.117582241918006E-22
        && 0 <= qq(4) && qq(4) <= 1.2621773731219804E-29
        && 0 <= qq(5) && qq(5) <= 7.5231633968471315E-37
        && 0 <= qq(6) && qq(6) <= 4.4841548185629436E-44
        && 0 <= qq(7) && qq(7) <= 2.6727645507830045E-51
        && 0 <= qq(8) && qq(8) <= 1.5930918161767748E-58
        && 0 <= qq(9) && qq(9) <= 9.495567179779856E-66
        && 0 <= qq(10) && qq(10) <= 5.659799086916361E-73
        && 0 <= qq(11) && qq(11) <= 3.373503140757299E-80
        && 0 <= qq(12) && qq(12) <= 2.0107645635350341E-87
        && 0 <= qq(13) && qq(13) <= 1.1985090753644908E-94
        && 0 <= qq(14) && qq(14) <= 7.143670769718235E-102
        && 0 <= qq(15) && qq(15) <= 4.257959586213967E-109
        && 0 <= qq(16) && qq(16) <= 2.5379416860425275E-116
        && 0 <= qq(17) && qq(17) <= 1.5127311265722081E-123
        && 0 <= qq(18) && qq(18) <= 9.016580144001294E-131
        && 0 <= qq(19) && qq(19) <= 5.374300565720376E-138
    }

    private val fqBound = Array[Double](
      0.785398032021746,
      1.3137568957176623E-7,
      1.2775764834046103E-14,
      1.0862386096603872E-21,
      8.087927686569757E-29,
      5.199465491241273E-36,
      3.09912293627338E-43,
      1.8472212173184038E-50,
      1.101029644798281E-57,
      6.562648086537606E-65,
      3.91164307983971E-72,
      2.3315209626196086E-79,
      1.3896947876331858E-86,
      8.283226416308795E-94,
      4.937187681382176E-101,
      2.942793179382191E-108,
      1.7540414210451787E-115,
      1.0454901582271926E-122,
      6.231606949729875E-130,
      3.714327186185047E-137,
    )

    @pure
    private def fqInv(fq: Array[Double]): Boolean = {
      fq.length == 20 && all20(fq, !_.isNaN)
        && 0 <= fq(0) && fq(0) <= 0.785398032021746
        && 0 <= fq(1) && fq(1) <= 1.3137568957176623E-7
        && 0 <= fq(2) && fq(2) <= 1.2775764834046103E-14
        && 0 <= fq(3) && fq(3) <= 1.0862386096603872E-21
        && 0 <= fq(4) && fq(4) <= 8.087927686569757E-29
        && 0 <= fq(5) && fq(5) <= 5.199465491241273E-36
        && 0 <= fq(6) && fq(6) <= 3.09912293627338E-43
        && 0 <= fq(7) && fq(7) <= 1.8472212173184038E-50
        && 0 <= fq(8) && fq(8) <= 1.101029644798281E-57
        && 0 <= fq(9) && fq(9) <= 6.562648086537606E-65
        && 0 <= fq(10) && fq(10) <= 3.91164307983971E-72
        && 0 <= fq(11) && fq(11) <= 2.3315209626196086E-79
        && 0 <= fq(12) && fq(12) <= 1.3896947876331858E-86
        && 0 <= fq(13) && fq(13) <= 8.283226416308795E-94
        && 0 <= fq(14) && fq(14) <= 4.937187681382176E-101
        && 0 <= fq(15) && fq(15) <= 2.942793179382191E-108
        && 0 <= fq(16) && fq(16) <= 1.7540414210451787E-115
        && 0 <= fq(17) && fq(17) <= 1.0454901582271926E-122
        && 0 <= fq(18) && fq(18) <= 6.231606949729875E-130
        && 0 <= fq(19) && fq(19) <= 3.714327186185047E-137
    }

    private val sBound = Array[Double](
      0.7853981633974483,
      1.3137570234753214E-7,
      1.2775765920284793E-14,
      1.0862386905396692E-21,
      8.087928206516337E-29,
      5.1994658011535854E-36,
      3.099123120995513E-43,
      1.8472213274213748E-50,
      1.1010297104247658E-57,
      6.562648477701937E-65,
      3.91164331299182E-72,
      2.3315211015890957E-79,
      1.3896948704654549E-86,
      8.283226910027593E-94,
      4.937187975661512E-101,
      2.9427933547863434E-108,
      1.7540415255942007E-115,
      1.0454902205432658E-122,
      6.2316073211625935E-130,
      3.714327186185047E-137,
    )

    //// Implementations of the main parts of the algorithm ////

    /**
     * Split the input into an array of 24-bit integer chunks, represented using doubles.
     * Leading zeros may be inserted to ensure the exponents of the chunks are multiples of `24`.
     *
     * @param x finite double to split
     * @return `(e, xx)` where `e % 24 == 0` and `x == (for (i <- 0 to 4) yield xx[i] * math.scalb(1.0d, e - 24 * i)).sum` TODO: test
     */
    @opaque
    @pure
    private def splitInput(x: Double): (Int, Array[Double]) = {
      require(x.isFinite && 1d <= x)
      val hx = __HI(x)
      val ix = hx & EXP_SIGNIF_BITS
      val e0 = (ix >> 20) - 1046 // exponent - 23
      assert(-23 <= e0 && e0 <= 1000)
      val e = {
        val tmp = 24 * ((e0 + 23) / 24)
        if tmp < 24 then 24 else tmp
      }
      assert(24 <= e && e <= 1008 && e % 24 == 0)
      val xx = new Array[Double](5)
      val i0 = __HI(__LO(0.0d, __LO(x)), ix - (e << 20)) // math.scalb(x, -e)
      xx(0) = i0.toInt.toDouble
      val i1 = (i0 - xx(0)) * TWO24
      xx(1) = i1.toInt.toDouble
      val i2 = (i1 - xx(1)) * TWO24
      xx(2) = i2.toInt.toDouble
      val i3 = (i2 - xx(2)) * TWO24
      xx(3) = i3.toInt.toDouble
      val i4 = (i3 - xx(3)) * TWO24
      xx(4) = i4.toInt.toDouble
      (e, xx)
    }.ensuring(res =>
      24 <= res._1 && res._1 <= 1008 && res._1 % 24 == 0
        && xxInv(res._2)
    )

    /**
     * Multiply a double, represented using 24-bit chunks as `(e, xx)`, by two over pi.
     * For efficiency, parts of the result not relevant to the Payne-Hanek range reduction are not computed.
     * Modulo `2^24`, the result is computed within `2^-(24 * jz - 28)` of the real-valued result.
     *
     * @param jz used to select precision of the result
     * @param e  exponent of first bit-chunk of the input double
     * @param xx the 24-bit integer chunks of the input double
     * @return the result as an array of 51-bit integer chunks where the exponent at index `i` is `-24 * i`
     */
    @opaque
    @pure
    private def timesTwoOverPi(jz: Int, e: Int, xx: Array[Double]): Array[Double] = {
      require(0 <= jz && jz <= 15)
      require(24 <= e && e <= 1008 && e % 24 == 0)
      require(xxInv(xx))

      val jx = xx.length - 1
      val jv = {
        val tmp = (e - 3) / 24
        if tmp < 0 then 0 else tmp
      }
      val q0 = e - 24 * (jv + 1)
      assert(q0 == 0) // sanity check since the input splitting is not implemented exactly as in the original

      val f = new Array[Double](20)
      var i = 0
      (while (i <= jx + jz) {
        decreases(jx + jz + 1 - i)
        if jv - jx + i >= 0 then f(i) = two_over_pi(jv - jx + i).toDouble
        i += 1
      }).invariant(
        0 <= i && i <= jx + jz + 1
          && fInv(f)
      )

      val q = new Array[Double](20)
      i = 0
      (while (i <= jz) {
        decreases(jz + 1 - i)
        q(i) = xx(0) * f(i + 4) + xx(1) * f(i + 3) + xx(2) * f(i + 2) + xx(3) * f(i + 1) + xx(4) * f(i)
        assert(Q(f(i + 4)))
        assert(Q(f(i + 3)))
        assert(Q(f(i + 2)))
        assert(Q(f(i + 1)))
        assert(Q(f(i)))
        assert(P(q(i)))
        i += 1
      }).invariant(
        0 <= i && i <= jz + 1
          && fInv(f)
          && qInv(q)
      )

      // If it were computed, `q(jz + 1)` would be a 51-bit integer.
      // Hence, less than "28 bits" are missing from the computed part of `q`.
      // Thus, the result is computed within `2^-(24 * jz - 28)` of the real result, modulo 2^24.
      // (Carry terms from `q(jz + 2)`, `q(jz + 3)`, etc. should not affect this, see e.g. the bounds on `z` in `computeModulo()`.)
      q
    }.ensuring(res => qInv(res))

    /**
     * Compute `n` and `r` such that the input modulo `2 * pi` is `n * (pi / 4) + r`.
     *
     * @param jz highest index of `q` containing part of the input
     * @param q  input represented using 51-bit integer chunks where index `i` has exponent `-24 * i`
     * @return `(n, neg, oneHalf, qq)` where `qq` represents the absolute value of `r` using 24-bit chunks where
     *         index `i` has exponent `-24 * i`, `neg` is true iff `r` is negative, and `oneHalf` is true if `r == 0.5`.
     */
    @opaque
    @pure
    private def computeModulo(jz: Int, q: Array[Double]): (Int, Boolean, Boolean, Array[Double]) = {
      require(2 <= jz && jz < 19)
      require(qInv(q))

      val iq = new Array[Int](20)
      var j = jz
      var z = q(jz)
      //      val fw0 = (twon24 * z).toInt.toDouble
      //      iq(jz - j) = (z - TWO24 * fw0).toInt
      //      assert(QInt(iq(jz - j)))
      //      assert(0 <= fw0 && fw0 <= 0x500_0002)
      //      assert(P(q(j - 1)))
      //      z = q(j - 1) + fw0
      //      j -= 1
      //      val fw1 = (twon24 * z).toInt.toDouble
      //      iq(jz - j) = (z - TWO24 * fw1).toInt
      //      assert(QInt(iq(jz - j)))
      //      assert(0 <= fw1 && fw1 <= 0x500_0004)
      //      assert(P(q(j - 1)))
      //      z = q(j - 1) + fw1
      //      j -= 1
      (while (j > 0) {
        decreases(j)
        val fw = (twon24 * z).toInt.toDouble
        iq(jz - j) = (z - TWO24 * fw).toInt
        assert(QInt(iq(jz - j)))
        assert(0 <= fw && fw <= 0x500_0004)
        assert(P(q(j - 1)))
        z = q(j - 1) + fw
        j -= 1
      }).invariant(
        0 <= j && j <= jz
          && !z.isNaN && 0 <= z && z <= 5 * 0xffff_ffff_ffffL + 0x500_0004
          && iqInv(iq)
      )

      z -= 8.0d * (z * 0.125).toLong.toDouble
      assert(0 <= z && z < 8)
      val neg = iq(jz - 1) >= 0x80_0000
      val n = if neg then (z.toInt + 1) & 7 else z.toInt

      var carry = 0
      if (neg) {
        var i = 0
        (while (i < jz - 1) {
          decreases(jz - i)
          val j = iq(i)
          assert(QInt(j))
          iq(i) = if carry == 0 then if j != 0 then 0x100_0000 - j else 0 else 0xff_ffff - j
          carry = if carry == 0 && j != 0 then 1 else carry
          i += 1
        }).invariant(
          0 <= i && i <= jz - 1
            && iqInv(iq) && iq(jz - 1) >= 0x80_0000
            && (carry == 0 || carry == 1)
        )
        val j = iq(jz - 1)
        iq(jz - 1) = if carry == 0 then 0x100_0000 - j else 0xff_ffff - j
      }

      assert(0 <= iq(jz - 1) && iq(jz - 1) <= 0x80_0000)
      val oneHalf = neg && carry == 0 && iq(jz - 1) == 0x80_0000

      val qq = new Array[Double](20)
      assert(qqInv(qq))
      if (!oneHalf) {
        assert(iq(jz - 1) <= 0x7f_ffff)
        var i = 0
        (while (i < jz) {
          decreases(jz - i)
          assert(QInt(iq(jz - 1 - i)))
          qq(i) = twon24Pow(i + 1) * iq(jz - 1 - i)
          assert(0 <= qq(i) && qq(i) <= qqBound(i))
          assert(qq.length == 20 && qqInv(qq))
          i += 1
        }).invariant(
          0 <= i && i <= jz
            && iqInv(iq) && iq(jz - 1) <= 0x7f_ffff
            && qq.length == 20 && qqInv(qq)
        )
      }

      (n, neg, oneHalf, qq)
    }.ensuring(res =>
      0 <= res._1 && res._1 < 8
        && res._4.length == 20 && qqInv(res._4)
    )

    /**
     * Multiply the input by 120 bits of pi over two.
     *
     * @param jz number of leading elements of `qq` containing part of the input
     * @param qq the input represented by 24-bit chunks
     * @return an array representing the result as an unevaluated sum
     */
    @opaque
    @pure
    private def timesPiOverTwo(jz: Int, qq: Array[Double]): Array[Double] = {
      require(0 <= jz && jz < 20)
      require(qq.length == 20 && qqInv(qq))
      val fq = new Array[Double](20)
      fq(0) = PIo2(0) * qq(0)
      assert(0 <= fq(0) && fq(0) <= fqBound(0))
      fq(1) = PIo2(0) * qq(1) + PIo2(1) * qq(0)
      assert(0 <= fq(1) && fq(1) <= fqBound(1))
      fq(2) = PIo2(0) * qq(2) + PIo2(1) * qq(1) + PIo2(2) * qq(0)
      assert(0 <= fq(2) && fq(2) <= fqBound(2))
      fq(3) = PIo2(0) * qq(3) + PIo2(1) * qq(2) + PIo2(2) * qq(1) + PIo2(3) * qq(0)
      assert(0 <= fq(3) && fq(3) <= fqBound(3))
      var i = 4
      (while (i < jz) {
        decreases(jz - i)
        val fw0 = PIo2(0) * qq(i - 0)
        val fw1 = PIo2(1) * qq(i - 1)
        val fw2 = PIo2(2) * qq(i - 2)
        val fw3 = PIo2(3) * qq(i - 3)
        val fw4 = PIo2(4) * qq(i - 4)
        val fw = fw0 + fw1 + fw2 + fw3 + fw4
        assert(0 <= fw0 && fw0 <= PIo2(0) * qqBound(i - 0))
        assert(0 <= fw1 && fw1 <= PIo2(1) * qqBound(i - 1))
        assert(0 <= fw2 && fw2 <= PIo2(2) * qqBound(i - 2))
        assert(0 <= fw3 && fw3 <= PIo2(3) * qqBound(i - 3))
        assert(0 <= fw4 && fw4 <= PIo2(4) * qqBound(i - 4))
        assert(0 <= fw && fw <= fqBound(i))
        fq(i) = fw
        i += 1
      }).invariant(
        4 <= i && i <= jz
          && qq.length == 20 && qqInv(qq)
          && fq.length == 20 && fqInv(fq)
      )
      fq
    }.ensuring(res =>
      res.length == 20 && fqInv(res)
    )

    private def fast2Sum(a: Double, b: Double): (Double, Double) = {
      require((a + b).isFinite)
      require((if a < 0 then -a else a) >= (if b < 0 then -b else b))
      val s = a + b
      (s, a - s + b)
    }.ensuring(res => res._1 + res._2 == res._1)

    //    private def twoSum(a: Double, b: Double): (Double, Double) = {
    //      require((a + b).isFinite)
    //      require((2 * a).isFinite)
    //      require((2 * b).isFinite)
    //      val s = a + b
    //      val a1 = s - b
    //      val b1 = s - a1
    //      val da = a - a1
    //      val db = b - b1
    //      val t = da + db
    //      (s, t)
    //    }.ensuring(res => res._1 + res._2 == res._1)

    /**
     * Compress the input to a double-double representation (a double plus a compensation term).
     *
     * @param jz  number of leading elements of `fq` containing part of the input
     * @param fq  the input represented as an unevaluated sum
     * @param neg true iff the input is negative
     * @return the input represented as a double-double
     */
    @opaque
    @pure
    private def fqCompression(jz: Int, fq: Array[Double], neg: Boolean): (Double, Double) = {
      require(fq.length == 20 && fqInv(fq))
      require(0 <= jz && jz < 20)
      var s = 0.0d
      var c = 0.0d
      var i = jz - 1
      // Coincidentally, this seems to be very similar to the XBLAS sum algorithm.
      (while (i >= 0) {
        decreases(i + 1)
        assert(0 <= s && s <= 1)
        val (s1, c1) = if s >= fq(i) then fast2Sum(s, fq(i)) else fast2Sum(fq(i), s)
        assert(s1 >= c + c1)
        val (s2, c2) = fast2Sum(s1, c + c1)
        s = s2
        c = c2
        i -= 1
      }).invariant(
        -1 <= i && i <= jz - 1
          && !s.isNaN && !c.isNaN && 0 <= s && s <= sBound(i + 1) && s + c == s
          && fq.length == 20 && fqInv(fq)
      )
      if neg then (-s, -c) else (s, c)
    }.ensuring(res =>
      -0.7853981633974483 <= res._1 && res._1 <= 0.7853981633974483 && res._1 + res._2 == res._1
    )

    //// The range reduction algorithm ////

    /**
     * Compute `x mod pi / 2` using the Payne-Hanek method,
     * returning `y` in `[-pi / 4, pi / 4]` and `n` in `[0, 8)` such that `x == n * (pi / 4) + y` modulo `pi / 2`.
     *
     * @param x finite double to compute modulo `pi / 2`
     * @return `(n, y0, y1)` where `y` is the unevaluated sum `y0 + y1`.
     */
    @opaque
    @pure
    def __kernel_rem_pio2(x: Double): (Int, Double, Double) = {
      require(x.isFinite && 1d <= x)

      // Here, `x * (2 / pi) mod 1` is computed within `2^-(24 * jz - 28)` of the real-valued result.
      // The worst-case input, the double closest to a multiple of `pi / 2`, is `5.319372648326541E255`, for which
      // there is 61 "extra" leading zeros in `x * (2 / pi) mod 1` due to cancellation.
      // Hence, for correct rounding, we need to compute `x * (2 / pi) mod 1`
      // within `2^-(61 + (desired precision) + 1)` of the real-valued result.
      // Thus, `jz = 6` yields at least 54 "correct bits" of `x * (2 / pi) mod 1`, and `jz = 7` yields 78.
      //
      // In practice, a lower value of `jz` is often sufficient.
      // Empirically, for 10's of billions of random doubles, and all single precision numbers
      // using `jz = 5` was sufficient to compute `sin` and `cos` with 1 ulp of a reference implementation.
      // For `5.319372648326541E255` `sin` was computed within 1 ulp, but not `cos`.
      // For `jz = 4`, a 1 ulp result, compared to a reference implementation, was obtained for:
      // - `cos()` for 9999997353/10000000000 random doubles (all except 2647)
      // - `cos()` for all single precision numbers except 632
      // - `sin()` for 9999997427/10000000000 random doubles (all except 2573)
      // - `sin()` for all single precision numbers except 632
      // - `sin()` for the worst-case input (but not for `cos()`)
      // But, being within 1 ulp of a reference implementation does not necessarily imply being withing 1 ulp of the correct result.
      // A possible performance optimization is to use an adaptive number of bits of `2 / pi`.

      // TODO: test against OpenJDK's FdLibm implementation
      // TODO: proof might be faster if `jz` is moved to the object and removed as a parameter to the methods.

      val jz = 6
      val (e, xx) = splitInput(x)
      val q = timesTwoOverPi(jz, e, xx)
      val (n, neg, oneHalf, qq) = computeModulo(jz, q)
      if (oneHalf)
        // This case should be unreachable, assuming sufficient precision is used.
        // But, it is currently challenging to impossible to show this in stainless.
        // It is simpler to just treat `x * (2 / pi) mod 1 ~== 0.5` as a special case.
        (n, 0.7853981633974483d, 9.615660845819876E-18)
      else {
        val fq = timesPiOverTwo(jz, qq)
        val (y0, y1) = fqCompression(jz, fq, neg)
        (n, y0, y1)
      }
    }.ensuring(res =>
      0 <= res._1 && res._1 < 8
        && -0.7853981633974483d <= res._2 && res._2 <= 0.7853981633974483d
        && res._2 + res._3 == res._2
    )
  }

  @library
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

    @opaque
    def compute(x: Double): Double = {
      if x.isNaN then Double.NaN
      else
        val hx = __HI_CHECKED(x)
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

  @library
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

    @opaque
    def compute(x: Double): Double = {
      if x.isNaN then Double.NaN
      else
        val hx = __HI_CHECKED(x)
        val ix = hx & EXP_SIGNIF_BITS
        if ix >= 0x3ff0_0000 then // |x| >= 1
          if ((ix - 0x3ff0_0000) | __LO_CHECKED(x)) == 0 then // |x| == 1
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
          val df = __LO_CHECKED(s, 0)
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
//      && ((x.isFinite && -1.0d <= x && x <= 1.0d) ==> (res.isFinite && res.isPositive && 0 <= res && res <= stainless.math.Pi))
    )
  }

  @library
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

    @opaque
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
      && (!x.isNaN == (!res.isNaN && (- Pi / 2 <= res && res <= Pi / 2)))
      && (x.isPosInfinity ==> (res == Pi / 2))
      && (x.isNegInfinity ==> (res == -Pi / 2))
    )
  }

  @library
  object Atan2 {
    private val tiny = 1.0e-300
    private val pi_o_4 = java.lang.Double.longBitsToDouble(0x3fe921fb54442d18L)
    private val pi_o_2 = java.lang.Double.longBitsToDouble(0x3ff921fb54442d18L)
    private val pi_lo = java.lang.Double.longBitsToDouble(0x3ca1a62633145c07L)

    @opaque
    def compute(y: Double, x: Double): Double = {
      if x.isNaN || y.isNaN then x + y
      else
        val hx = __HI(x)
        val ix = hx & EXP_SIGNIF_BITS
        val lx = __LO(x)
        val hy = __HI(y)
        val iy = hy & EXP_SIGNIF_BITS
        val ly = __LO(y)


        if (math.wrapping(hx - 0x3ff0_0000) | lx) == 0 then Atan.compute(y) // x = 1.0
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

  @library
  object Cbrt {
    // unsigned
    private val B1 = 715094163
    private val B2 = 696219795
    private val C = 19.0/35.0
    private val D = -864.0/1225.0
    private val E = 99.0/70.0
    private val F = 45.0/28.0
    private val G = 5.0/14.0

    @opaque
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
            __HI_CHECKED(temp_t, __HI_CHECKED(temp_t) / 3 + B2)
          else
            val hx = __HI_CHECKED(x_abs) // high word of x
            __HI_CHECKED(0.0, hx / 3 + B1)

        // New cbrt to 23 bits, may be implemented in single precision
        val r = t * t / x_abs
        val s = C + r * t
        // Chopped to 20 bits and make it larger than cbrt(x)
        val t2 = __LO_CHECKED(t * (G + F / (s + E + D / s)), 0)
        val t3 = __HI_CHECKED(t2, __HI_CHECKED(t2) + 0x00000001)
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
        ((!x.isNaN && x == 1) ==> (res == 1)) &&
        ((!x.isNaN && x == -1) ==> (res == -1)) &&
        (x.isPositive == res.isPositive) &&
        (x.isNegative == res.isNegative) &&
        ((x.isFinite && stainless.math.abs(x) > 1) ==> stainless.math.abs(res) < stainless.math.abs(x)) &&
        ((x.isFinite && !x.isZero && stainless.math.abs(x) < 1) ==> stainless.math.abs(res) > stainless.math.abs(x))
      )
  }

  @library
  object Hypot {
    private val TWO_MINUS_600: Double = java.lang.Double.longBitsToDouble(0x1a70000000000000L)
    private val TWO_PLUS_600: Double = java.lang.Double.longBitsToDouble(0x6570000000000000L)

    @opaque
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
          val cond1 = big > java.lang.Double.longBitsToDouble(0x5f300000ffffffffL)
          val k: Int = if cond1 then 600 else 0
          val hbig2 = if cond1 then hbig - 0x25800000 else hbig
          val hsmall2 = if cond1 then hsmall - 0x25800000 else hsmall
          val big2 = if cond1 then big * TWO_MINUS_600 else big
          val small2 = if cond1 then small * TWO_MINUS_600 else small

          if small == 0 then big
          else
            val cond2 = small2 < java.lang.Double.longBitsToDouble(0x20b0000000000000L) // small < 2**-500
            val cond3 = small2 < stainless.DoubleConsts.MIN_NORMAL // subnormal b or 0
            val t1 = if cond2 && cond3 then java.lang.Double.longBitsToDouble(0x7fd0000000000000L) else 0.0
            val small3 = if cond2 then if cond3 then small2 * t1 else small2 * TWO_PLUS_600 else small2
            val big3 = if cond2 then if cond3 then big2 * t1 else big2 * TWO_PLUS_600 else big2
            val k2 = if cond2 then if cond3 then k - 1022 else k - 600 else k
            val hbig3 = if cond2 then if cond3 then hbig2 else hbig2 + 0x25800000 else hbig2
            val hsmall3 = if cond2 then if cond3 then hsmall2 else hsmall2 + 0x25800000 else hsmall2

            val w: Double = big3 - small3

            val cond4 = w > small3
            val t11 = if cond4 then __HI(0.0, hbig3) else __HI(0.0, hbig3 + 0x00100000)
            val big4 = if cond4 then big3 else big3 + big3
            val t2 = big4 - t11
            val y1 = if cond4 then 0.0 else __HI(0.0, hsmall3)
            val y2 = if cond4 then 0.0 else small3 - y1
            val w2 =
              if cond4 then stainless.math.sqrt(t11 * t11 - (small3 * (-small3) - t2 * (big4 + t11)))
              else stainless.math.sqrt(t11 * y1 - (w * (-w) - (t11 * y2 + t2 * small3)))

            if k2 != 0 then stainless.math.powerOfTwoD(k2) * w2 else w2

    }.ensuring(res =>
      ((x.isInfinity || y.isInfinity) ==> res.isPosInfinity) &&
      (res.isNaN == (!x.isInfinity && !y.isInfinity && (x.isNaN || y.isNaN))) &&
      (!res.isNaN == res.isPositive) &&
      ((x.isZero && !y.isNaN) ==> (res == stainless.math.abs(y))) &&
      ((y.isZero && !x.isNaN) ==> (res == stainless.math.abs(x)))
    )
  }

  @library
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

    @opaque
    def compute(xInit: Double): Double = {

      if xInit.isNaN then Double.NaN
      else

        var hxInit = __HI_CHECKED(xInit) // high word of x
        val lx = __LO_CHECKED(xInit) // low  word of x, unsigned

        if hxInit < 0x0010_0000 && (((hxInit & EXP_SIGNIF_BITS) | lx) == 0) then -TWO54 / 0.0
        else if hxInit < 0 then (xInit - xInit) / 0.0
        else
          val xInit2 = if hxInit < 0x0010_0000 then xInit * TWO54 else xInit
          val hxInit2 = if hxInit < 0x0010_0000 then __HI_CHECKED(xInit2) else hxInit

          if hxInit2 >= EXP_BITS then  xInit2 + xInit2
          else
            val kInit: Int = (if hxInit < 0x0010_0000 then -54 else 0) + ((hxInit2 >> 20) - 1023)
            val hx: Int = hxInit2 & 0x000f_ffff
            val i: Int = (hx + 0x9_5f64) & 0x10_0000
            val x: Double = __HI_CHECKED(xInit2, hx | (i ^ 0x3ff0_0000)) // normalize x or x/2

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

  @library
  object Log10 {
    private val ivln10 = java.lang.Double.longBitsToDouble(0x3fdbcb7b1526e50eL) // 4.34294481903251816668e-01
    private val log10_2hi = java.lang.Double.longBitsToDouble(0x3fd34413509f6000L) // 3.01029995663611771306e-01;
    private val log10_2lo = java.lang.Double.longBitsToDouble(0x3d59fef311f12b36L) // 3.69423907715893078616e-13;

    @opaque
    def compute(x: Double): Double = {
      val hx = __HI(x) // high word of x
      val lx = __LO(x) // low word of x
      if (hx < 0x0010_0000) && (((hx & EXP_SIGNIF_BITS) | lx) == 0) then -TWO54 / 0.0
      else if hx < 0 then (x - x) / 0.0
      else
        val k = if hx < 0x0010_0000 then -54 else 0
        val x2 = if hx < 0x0010_0000 then x * TWO54 else x
        val hx2 = if hx < 0x0010_0000 then __HI_CHECKED(x2) else hx

        if hx2 >= EXP_BITS then
          x2 + x2
        else
          val k2 = k + (hx2 >> 20) - 1023
          val i  = (k2  & SIGN_BIT) >>> 31
          val y = (k2 + i).toDouble
          (y * log10_2lo + ivln10 * Log.compute(__HI_CHECKED(x2, (hx2 & 0x000f_ffff) | ((0x3ff - i) << 20)))) + y * log10_2hi
    }.ensuring( res =>
      (res.isNaN == (x.isNaN || x < 0))
        && (x.isZero == res.isNegInfinity)
        && ((!x.isNaN && x == 1.0) ==> (res.isZero && res.isPositive))
        && ((!x.isNaN && x >= 1.0) == res.isPositive)
        && (res.isNegative ==> (x < 1.0))
        && ((x.isFinite && x >= 0) ==> res < x)
        && (x.isPosInfinity == res.isPosInfinity)
    )
  }

  @library
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

    @opaque
    def compute(x: Double): Double = {

      if x.isNaN then Double.NaN else
        val hx: Int = __HI_CHECKED(x)
        /* high word of x */
        val xsb: Int = (hx >> 31) & 1
        /* sign bit of x */
        val hx2: Int = hx & EXP_SIGNIF_BITS /* high word of |x| */

        /* filter out non-finite argument */
        if hx2 >= 0x40862E42 && (hx2 >= 0x7ff00000 || x > o_threshold || x < u_threshold) then
          /* if |x| >= 709.78... */
          if hx2 >= 0x7ff00000 then
            if ((hx2 & 0xfffff) | __LO_CHECKED(x)) != 0 then x + x /* NaN */
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
            if k >= -1021 then __HI_CHECKED(y, __HI_CHECKED(y) + (k << 20)) /* add k to y's exponent */
            else __HI_CHECKED(y, __HI_CHECKED(y) + ((k + 1000) << 20)) * twom1000
    }.ensuring(res =>
      res.isNaN == x.isNaN
      && (x.isPosInfinity ==> res.isPosInfinity)
      && (x.isNegInfinity ==> (res.isZero && res.isPositive))
      && (x.isZero ==> (res == 1))
      && ((!x.isNaN && x.isPositive) ==> res >= 1) // Converse does not hold: x = -7.458340731200206E-155
      && ((!x.isNaN && x.isNegative) ==> (res.isPositive && res <= 1))
    )
  }

  @library
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

    @opaque
    def compute(x: Double): Double = {
      if x.isNaN then Double.NaN else
        val hx = __HI_CHECKED(x) // high word of x
        val xsb = hx & SIGN_BIT // sign bit of x
        val y = stainless.math.abs(x)
        val hx2: Int = hx & EXP_SIGNIF_BITS /* high word of |x| */


        /* filter out non-finite argument */
        if hx2 >= 0x4043_687A && ((hx >= 0x4086_2E42 && (hx2 >= 0x7ff00000 || x > o_threshold)) || (xsb != 0 && x + tiny < 0.0)) then
          if hx >= 0x4086_2E42 then
            /* if |x| >= 709.78... */
            if hx2 >= 0x7ff00000 then
              if ((hx2 & 0xfffff) | __LO_CHECKED(x)) != 0 then x + x /* NaN */
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
                __HI_CHECKED(y, __HI_CHECKED(y) + (k << 20)) - 1.0 // add k to y's exponent
              else
                if k < 20 then
                  val t = __HI_CHECKED(1.0, 0x3ff0_0000 - (0x2_00000 >> k)) // t = 1-2^-k
                  val y = t - (e - x2)
                  __HI_CHECKED(y, __HI_CHECKED(y) + (k << 20)) // add k to y's exponent
                else
                  val t = __HI_CHECKED(1.0, ((0x3ff - k) << 20)) // 2^-k
                  val y = (x2 - (e + t)) + 1
                  __HI_CHECKED(y, __HI_CHECKED(y) + (k << 20)) // add k to y's exponent
    }.ensuring(res =>
      (res.isNaN == x.isNaN)
        && (x.isPosInfinity ==> res.isPosInfinity)
        && (x.isNegInfinity ==> (res == -1))
        && (x.isZero ==> (res == 0))
        && (x.isPositive == res.isPositive)
        && ((!x.isNaN) ==> (-1 <= res))
    )
  }

  @library
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

    @opaque
    def compute(x: Double): Double = {
      if x.isNaN then Double.NaN
      else
        val hx: Int = __HI_CHECKED(x) /* high word of x */
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
            val hu: Int = if k != 0 then __HI_CHECKED(u) else huInit
            val k2: Int = if k != 0 then (hu >> 20) - 1023 else k
            val c: Double = if k != 0 then if hx < 0x4340_0000 then (if k2 > 0 then 1.0 - (u - x) else x - (u - 1.0)) / u else 0 else 0.0
            val hu2: Int = if k != 0 then hu & 0x000f_ffff else hu
            val k3 = if (k != 0) && !(hu2 < 0x6_a09e) then k2 + 1 else k2
            val u2 = if k != 0 then if hu2 < 0x6_a09e then __HI_CHECKED(u, hu2 | 0x3ff0_0000) else __HI_CHECKED(u, hu2 | 0x3fe0_0000) else u
            val f2 = if k != 0 then u2 - 1.0 else f
            val hu3 = if k != 0 then if hu2 < 0x6_a09e then hu2 else (0x0010_0000 - hu2) >> 2 else hu2


            val hfsq = 0.5 * f2 * f2
            if hu3 == 0 then
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
        && (x.isPosInfinity == res.isPosInfinity)
    )
  }

  @library
  object Sinh {
    private val shuge = 1.0e307

    @opaque
    def compute(x: Double): Double = {

      if x.isNaN then Double.NaN else
        // High word of |x|
        val jx = __HI_CHECKED(x)
        val ix = jx & EXP_SIGNIF_BITS
        // x is INF or NaN
        if ix >= EXP_BITS then x + x
        else
          val h = if jx < 0 then -0.5 else 0.5

          // |x| in [0,22], return sign(x)*0.5*(E+E/(E+1)))
          if ix < 0x4036_0000 then // |x| < 22
            if (ix < 0x3e30_0000) && (shuge + x > 1.0) then x // sinh(tiny) = tiny with inexact // |x| < 2**-28
            else
              val t = Expm1.compute(stainless.math.abs(x))
              unfold(Expm1.compute(stainless.math.abs(x)))
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
        && (x.isZero == res.isZero)
        && (x.isPositive == res.isPositive)
        && (x.isNegative == res.isNegative)
    )
  }

  @library
  object Cosh {
    private val huge = 1.0e300
    @opaque
    def compute(x: Double): Double = {
      if x.isNaN then Double.NaN
      else
        // High word of |x|
        val ix = __HI_CHECKED(x) & EXP_SIGNIF_BITS
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
//              unfold(Exp.compute(stainless.math.abs(x)))
              0.5 * t + 0.5 / t
            else
              // |x| in [22, log(maxdouble)] return 0.5*exp(|x|)
              if ix < 0x4086_2E42 then {
//                unfold(Exp.compute(stainless.math.abs(x)))
                0.5 * Exp.compute(stainless.math.abs(x))
              } else
                // |x| in [log(maxdouble), overflowthreshold]
                val lx = __LO(x)
                if ix < 0x4086_33CE || ((ix == 0x4086_33ce) && (IntHelpers.compareUnsigned(lx, 0x8fb9_f87d) <= 0)) then
                  val w = Exp.compute(0.5 * stainless.math.abs(x))
//                  unfold(Exp.compute(0.5 * stainless.math.abs(x)))
                  val t = 0.5 * w
                  t * w
                else
                  // |x| > overflowthreshold, cosh(x) overflow
                  huge * huge
    }.ensuring(res =>
      (x.isNaN == res.isNaN)
//        && (!x.isNaN ==> (res >= 1))
        && (!x.isNaN ==> res.isPositive)
        && (x.isInfinity ==> res.isPosInfinity)
        && (x.isZero ==> (res == 1.0))
    )
  }

  @library
  object Tanh {
    private val tiny = 1.0e-300

    @opaque
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
      (x.isNaN == res.isNaN)
      && (!x.isNaN ==> (!res.isNaN && -1 <= res && res <= 1))
      && (x.isPositive ==> res >= 0)
      && (x.isNegative ==> res <= 0)
      && (x.isNegInfinity ==> (res == -1))
      && (x.isPosInfinity ==> (res == 1))
      && (x.isZero ==> res.isZero)
    )
  }

  @library
  object Pow {
    @opaque
    def compute(x: Double, y: Double): Double = {
      // y == zero: x**0 = 1
      if y.isZero then 1.0
      else if x.isNaN || y.isNaN then x + y
      else
        val y_abs = stainless.math.abs(y)
        val x_abs = stainless.math.abs(x)
        // Special values of y
        if y == 2.0 then x * x
        else if y == 0.5 && x >= -Double.MaxValue then stainless.math.sqrt(x + 0.0) // Add 0.0 to properly handle x == -0.0// Handle x == -infinity later
        else if y_abs == 1.0 then // y is  +/-1
          if y == 1.0 then x else 1.0 / x
        else if y_abs == Double.PositiveInfinity then // y is +/-infinity
          if x_abs == 1.0 then y - y // inf**+/-1 is NaN
          else if x_abs > 1.0 then // (|x| > 1)**+/-inf = inf, 0
            if y >= 0 then y else 0.0
          else if y < 0 then -y else 0.0 // (|x| < 1)**-/+inf = inf, 0
        else
          val hx = __HI_CHECKED(x)
          val ix = hx & EXP_SIGNIF_BITS
          val y_is_int =
            if hx < 0 then
              if y_abs >= java.lang.Double.longBitsToDouble(0x4340000000000000L) then 2
              else if y_abs >= 1.0 then // |y| >= 1.0
                  val y_abs_as_long = y_abs.toLong
                  if y_abs_as_long.toDouble == y_abs then
                    2 - (y_abs_as_long & 0x1L).toInt
                  else 0
              else 0
            else 0

          // Special value of x
          if x_abs == 0.0 || x_abs == Double.PositiveInfinity || x_abs == 1.0 then
            val z1 = if y < 0.0 then 1.0 / x_abs else x_abs
            if hx < 0 then
              if ((ix - 0x3ff00000) | y_is_int) == 0 then (z1 - z1) / (z1 - z1) // (-1)**non-int is NaN
              else if y_is_int == 1 then -1.0 * z1 // (x < 0)**odd = -(|x|**odd)
              else z1
            else z1
          else
            val n_init = (hx >> 31) + 1
            // (x < 0)**(non-int) is NaN
            if (n_init | y_is_int) == 0 then (x - x) / (x - x)
            else
              val s = if (n_init | (y_is_int - 1)) == 0 then -1.0 else 1.0 // (-ve)**(odd int)
              val y_large_cond: Boolean = y_abs > java.lang.Double.longBitsToDouble(0x41e00000ffffffffL)

              if y_large_cond && x_abs < java.lang.Double.longBitsToDouble(0x3fefffff00000000L) then
                if y < 0.0 then s * Double.PositiveInfinity else s * 0.0 // |x| < ~0.9999995231628418
              else if y_large_cond && x_abs > java.lang.Double.longBitsToDouble(0x3ff00000ffffffffL) then
                if y > 0.0 then s * Double.PositiveInfinity else s * 0.0
              else
                val INV_LN2 = java.lang.Double.longBitsToDouble(0x3ff71547652b82feL) //  1.44269504088896338700e+00 = 1/ln2
                val INV_LN2_H = java.lang.Double.longBitsToDouble(0x3ff7154760000000L) //  1.44269502162933349609e+00 = 24 bits of 1/ln2
                val INV_LN2_L = java.lang.Double.longBitsToDouble(0x3e54ae0bf85ddf44L) //  1.92596299112661746887e-08 = 1/ln2 tail

                val CP = java.lang.Double.longBitsToDouble(0x3feec709dc3a03fdL) //  9.61796693925975554329e-01 = 2/(3ln2)
                val CP_H = java.lang.Double.longBitsToDouble(0x3feec709e0000000L) //  9.61796700954437255859e-01 = (float)cp
                val CP_L = java.lang.Double.longBitsToDouble(0xbe3e2fe0145b01f5L) // -7.02846165095275826516e-09 = tail of CP_H

                val x_abs2: Double =
                  if y_large_cond then x_abs
                  else if ix < 0x00100000 then x_abs * java.lang.Double.longBitsToDouble(0x4340000000000000L) else x_abs
                // assert(x_abs2.isFinite && x_abs2.isPositive)

                val ix2: Int =
                  if y_large_cond then ix
                  else if ix < 0x00100000 then __HI(x_abs2) else ix

                val j: Int = if y_large_cond then 0 else ix2 & 0x000fffff

                // assert(0 <= j && j <= 0x000fffff)

                val n: Int =
                  if y_large_cond then n_init
                  else
                    val n2 = if ix < 0x00100000 then -53 else 0
                    val n3 = n2 + (ix2 >> 20) - 0x3ff
                    if !(j <= 0x3988E) && !(j < 0xBB67A) then n3 + 1 else n3
                val ix3: Int =
                  if y_large_cond then ix2
                  else j | 0x3ff00000
                val k: Int =
                  if y_large_cond then 0
                  else (if j <= 0x3988E then 0 else (if j < 0xBB67A then 1 else 0))
                val ix4: Int =
                  if y_large_cond then ix3
                  else if j > 0x3988E && j >= 0xBB67A then ix3 - 0x00100000 else ix3
                val x_abs3: Double =
                  if y_large_cond then x_abs2
                  else __HI(x_abs2, ix4)

                // assert(x_abs3.isFinite)

                val t: Double =
                  if y_large_cond then x_abs3 - 1.0
                  else n.toDouble

                // assert(t.isFinite)

                val w =
                  if y_large_cond then (t * t) * (0.5 - t * (0.3333333333333333333333 - t * 0.25))
                  else 0.0

                // assert(!w.isNaN)

                // Compute ss = s_h + s_l = (x-1)/(x+1) or (x-1.5)/(x+1.5)
                val BP = if k == 0 then 1.0 else 1.5
                val DP_H = if k == 0 then 0.0 else java.lang.Double.longBitsToDouble(0x3fe2b80340000000L) // 5.84962487220764160156e-01
                val DP_L = if k == 0 then 0.0 else java.lang.Double.longBitsToDouble(0x3e4cfdeb43cfd006L) // 1.35003920212974897128e-08

                // Poly coefs for (3/2)*(log(x)-2s-2/3*s**3
                val L1 = java.lang.Double.longBitsToDouble(0x3fe3333333333303L) //  5.99999999999994648725e-01
                val L2 = java.lang.Double.longBitsToDouble(0x3fdb6db6db6fabffL) //  4.28571428578550184252e-01
                val L3 = java.lang.Double.longBitsToDouble(0x3fd55555518f264dL) //  3.33333329818377432918e-01
                val L4 = java.lang.Double.longBitsToDouble(0x3fd17460a91d4101L) //  2.72728123808534006489e-01
                val L5 = java.lang.Double.longBitsToDouble(0x3fcd864a93c9db65L) //  2.30660745775561754067e-01
                val L6 = java.lang.Double.longBitsToDouble(0x3fca7e284a454eefL) //  2.06975017800338417784e-01

                val u: Double =
                  if y_large_cond then INV_LN2_H * t
                  else x_abs3 - BP

                // assert(u.isFinite)

                val v: Double =
                  if y_large_cond then t * INV_LN2_L - w * INV_LN2
                  else 1.0 / (x_abs3 + BP)

                // assert(v.isFinite)

                val ss = u * v

                // assert(ss.isFinite)

                val s_h = __LO(ss, 0)

                // assert(s_h.isFinite)

                val t_h = __HI(0.0, ((ix4 >> 1) | 0x20000000) + 0x00080000 + (k << 18))

                // assert(t_h.isPositive)

                val s_l = v * ((u - s_h * t_h) - s_h * (x_abs3 - (t_h - BP)))

                // assert(!s_l.isNaN)

                val s2 = ss * ss

                // assert(s2.isPositive)

                val r = (s2 * s2 * (L1 + s2 * (L2 + s2 * (L3 + s2 * (L4 + s2 * (L5 + s2 * L6)))))) + (s_l * (s_h + ss))

                // assert(!r.isNaN)

                val s3 = s_h * s_h

                // assert(s3.isFinite && s3.isPositive)

                val t_h2: Double = __LO((3.0 + s3 + r), 0)

                // assert(t_h2.isFinite)

                val t_l = r - ((t_h2 - 3.0) - s3)

                // assert(!t_l.isNaN)

                val u2 = if y_large_cond then u
                  else s_h * t_h2

                // assert(!u2.isNaN)

                val v2 = if y_large_cond then v
                  else s_l * t_h2 + t_l * ss

                // assert(!v2.isNaN)

                val p_h = __LO(u2 + v2, 0)

                // assert(!p_h.isNaN)
                val z_h = CP_H * p_h

                // assert(!z_h.isNaN)

                val z_l = CP_L * p_h + (v2 - (p_h - u2)) * CP + DP_L

                // assert(!z_l.isNaN)

                val t1 = if y_large_cond then p_h
                  else __LO((((z_h + z_l) + DP_H) + t), 0)

                // assert(!t1.isNaN)

                val t2 = if y_large_cond then v - (t1 - u)
                  else z_l - (((t1 - t) - DP_H) - z_h)

                // assert(!t2.isNaN)

                // Split up y into (y1 + y2) and compute (y1 + y2) * (t1 + t2)
                val y1: Double = __LO(y, 0)

                // assert(y1.isFinite)

                val p_l: Double = (y - y1) * t1 + y * t2
                val p_h2: Double = y1 * t1
                val z: Double = p_l + p_h2
                val j2: Int = __HI(z)
                val i: Int = __LO(z)

                // the two asserts below yield better strict-arithmetic verification times
                // assert(!p_l.isNaN)
                // assert(!(z - p_h2).isNaN)
                if j2 >= 0x40900000 && (((j2 - 0x40900000) | i) != 0 || p_l + 8.0085662595372944372e-0017 > z - p_h2) then s * Double.PositiveInfinity // Overflow
                else if (j2 & EXP_SIGNIF_BITS) >= 0x4090cc00 && (((j2 - 0xc090cc00) | i) != 0 || p_l <= z - p_h2) then s * 0.0
                else

                  // Poly coefs for (3/2)*(log(x)-2s-2/3*s**3
                  val P1 = java.lang.Double.longBitsToDouble(0x3fc555555555553eL) //  1.66666666666666019037e-01
                  val P2 = java.lang.Double.longBitsToDouble(0xbf66c16c16bebd93L) // -2.77777777770155933842e-03
                  val P3 = java.lang.Double.longBitsToDouble(0x3f11566aaf25de2cL) //  6.61375632143793436117e-05
                  val P4 = java.lang.Double.longBitsToDouble(0xbebbbd41c5d26bf1L) // -1.65339022054652515390e-06
                  val P5 = java.lang.Double.longBitsToDouble(0x3e66376972bea4d0L) //  4.13813679705723846039e-08
                  val LG2 = java.lang.Double.longBitsToDouble(0x3fe62e42fefa39efL) //  6.93147180559945286227e-01
                  val LG2_H = java.lang.Double.longBitsToDouble(0x3fe62e4300000000L) //  6.93147182464599609375e-01
                  val LG2_L = java.lang.Double.longBitsToDouble(0xbe205c610ca86c39L) // -1.90465429995776804525e-09

                  val i2 = j2 & EXP_SIGNIF_BITS
                  val k = (i2 >> 20) - 0x3ff
                  val m = if i2 > 0x3fe00000 then j2 + (0x00100000 >> (k + 1)) else 0
                  val k2 = if i2 > 0x3fe00000 then ((m & EXP_SIGNIF_BITS) >> 20) - 0x3ff else k
                  val p_h3 = if i2 > 0x3fe00000 then p_h2 - __HI(0.0, m & ~(0x000fffff >> k2)) else p_h2
                  val m2 = if i2 > 0x3fe00000 then ((m & 0x000fffff) | 0x00100000) >> (20 - k2) else m
                  val m3 = if i2 > 0x3fe00000 && j2 < 0 then -m2 else m2
                  val tt = __LO(p_l + p_h3, 0)
                  val uFinal = tt * LG2_H
                  val v3 = (p_l - (tt - p_h3)) * LG2 + tt * LG2_L
                  val z2 = uFinal + v3
                  val wFinal = v3 - (z2 - uFinal)
                  val tFinal = z2 * z2
                  val t1Final = z2 - tFinal * (P1 + tFinal * (P2 + tFinal * (P3 + tFinal * (P4 + tFinal * P5))))
                  val z3 = 1.0 - (((z2 * t1Final) / (t1Final - 2.0) - (wFinal + z2 * wFinal)) - z2)
                  // assert(!z3.isNaN)
                  val hi_z3 = __HI(z3)
                  val j3 = hi_z3 + (m3 << 20) // addition overflow check slow
                  // substituting j3 for hi_z3 + (m3 << 20) in the line below yields better strict-arithmetic performance
                  val z4 =
                    if (j3 >> 20) <= 0 then stainless.math.scalb(z3, m3) else __HI(z3, hi_z3 + (m3 << 20))
                  s * z4
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
  }

}
