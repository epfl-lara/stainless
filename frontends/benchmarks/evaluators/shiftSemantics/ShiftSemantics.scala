/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.math.Unsigned.*

/** Shifts by amounts outside of `[0, width)`, which both evaluators must
 *  compute as the JVM does, see
 *  https://github.com/epfl-lara/stainless/issues/1828. The amount of `Int` and
 *  `Long` shifts is taken modulo the width (`1 << 33 == 2`, `1 << -1 ==
 *  Int.MinValue`). `Byte` and `Short` operands are promoted to `Int` before
 *  shifting, so the amount is taken modulo 32 and the result is an `Int`.
 *  Shifting a `stainless.math.Unsigned` value by the size of its type or more
 *  gives 0, as in SMT-LIB.
 *
 *  Each `fooN` function is evaluated and compared to the literal returned by
 *  `expectedFooN`. The amounts are bound to `val`s so that the Scala compiler
 *  does not fold the shifts itself.
 */
object ShiftSemantics:

  // Int: the amount is taken modulo 32

  def shl31: Int =
    val n: Int = 31
    1 << n

  def expectedShl31: Int =
    -2147483648

  def shl33: Int =
    val n: Int = 33
    1 << n

  def expectedShl33: Int =
    2

  def shlNegative: Int =
    val n: Int = -1
    1 << n

  def expectedShlNegative: Int =
    -2147483648

  def shlMinValueNegative: Int =
    val n: Int = -1
    -2147483648 << n

  def expectedShlMinValueNegative: Int =
    0

  def ashr32: Int =
    val n: Int = 32
    -2147483648 >> n

  def expectedAshr32: Int =
    -2147483648

  def ashr33: Int =
    val n: Int = 33
    -2147483648 >> n

  def expectedAshr33: Int =
    -1073741824

  def ashrNegative: Int =
    val n: Int = -1
    -2147483648 >> n

  def expectedAshrNegative: Int =
    -1

  def lshr33: Int =
    val n: Int = 33
    -2147483648 >>> n

  def expectedLshr33: Int =
    1073741824

  def lshrNegative: Int =
    val n: Int = -1
    -1 >>> n

  def expectedLshrNegative: Int =
    1

  // Long: the amount is taken modulo 64

  def longShl65: Long =
    val n: Int = 65
    1L << n

  def expectedLongShl65: Long =
    2L

  def longShlNegative: Long =
    val n: Int = -1
    1L << n

  def expectedLongShlNegative: Long =
    -9223372036854775808L

  def longAshr64: Long =
    val n: Int = 64
    -9223372036854775808L >> n

  def expectedLongAshr64: Long =
    -9223372036854775808L

  def longAshr65: Long =
    val n: Int = 65
    -9223372036854775808L >> n

  def expectedLongAshr65: Long =
    -4611686018427387904L

  def longLshr65: Long =
    val n: Int = 65
    -9223372036854775808L >>> n

  def expectedLongLshr65: Long =
    4611686018427387904L

  def longShlLongAmount: Long =
    val n: Long = 4294967361L // 2^32 + 65
    1L << n

  def expectedLongShlLongAmount: Long =
    2L

  // Byte: promoted to Int, so the result does not wrap around at 8 bits and the amount is taken modulo 32

  def byteShl7: Int =
    val b: Byte = 1
    val n: Int = 7
    b << n

  def expectedByteShl7: Int =
    128

  def byteShl7ToByte: Byte =
    val b: Byte = 1
    val n: Int = 7
    (b << n).toByte

  def expectedByteShl7ToByte: Byte =
    -128

  def byteShl8: Int =
    val b: Byte = -1
    val n: Int = 8
    b << n

  def expectedByteShl8: Int =
    -256

  def byteShl33: Int =
    val b: Byte = 1
    val n: Int = 33
    b << n

  def expectedByteShl33: Int =
    2

  def byteShlNegative: Int =
    val b: Byte = 1
    val n: Int = -1
    b << n

  def expectedByteShlNegative: Int =
    -2147483648

  def byteShlByteAmount: Int =
    val b: Byte = 1
    val n: Byte = 33
    b << n

  def expectedByteShlByteAmount: Int =
    2

  def byteAshr33: Int =
    val b: Byte = -128
    val n: Int = 33
    b >> n

  def expectedByteAshr33: Int =
    -64

  def byteLshr33: Int =
    val b: Byte = -128
    val n: Int = 33
    b >>> n

  def expectedByteLshr33: Int =
    2147483584

  def byteLshrNegative: Int =
    val b: Byte = -128
    val n: Int = -1
    b >>> n

  def expectedByteLshrNegative: Int =
    1

  // Short: promoted to Int as well

  def shortShl15: Int =
    val s: Short = 1
    val n: Int = 15
    s << n

  def expectedShortShl15: Int =
    32768

  def shortShl15ToShort: Short =
    val s: Short = 1
    val n: Int = 15
    (s << n).toShort

  def expectedShortShl15ToShort: Short =
    -32768

  def shortShl16: Int =
    val s: Short = -1
    val n: Int = 16
    s << n

  def expectedShortShl16: Int =
    -65536

  def shortShl34: Int =
    val s: Short = 1
    val n: Int = 34
    s << n

  def expectedShortShl34: Int =
    4

  def shortShlNegative: Int =
    val s: Short = 1
    val n: Int = -1
    s << n

  def expectedShortShlNegative: Int =
    -2147483648

  def shortShlShortAmount: Int =
    val s: Short = 1
    val n: Short = 34
    s << n

  def expectedShortShlShortAmount: Int =
    4

  def shortAshr32: Int =
    val s: Short = -32768
    val n: Int = 32
    s >> n

  def expectedShortAshr32: Int =
    -32768

  def shortLshr33: Int =
    val s: Short = -32768
    val n: Int = 33
    s >>> n

  def expectedShortLshr33: Int =
    2147467264

  // UByte: 8-bit wrap-around, and 0 for amounts of 8 or more

  def ubyteShl4: UByte =
    val n: UByte = 4.toUByte
    0x0f.toUByte << n

  def expectedUbyteShl4: UByte =
    240.toUByte

  def ubyteShl1Wraps: UByte =
    val n: UByte = 1.toUByte
    0x81.toUByte << n

  def expectedUbyteShl1Wraps: UByte =
    2.toUByte

  def ubyteLshr4: UByte =
    val n: UByte = 4.toUByte
    0xf0.toUByte >>> n

  def expectedUbyteLshr4: UByte =
    15.toUByte

  def ubyteShl8: UByte =
    val n: UByte = 8.toUByte
    1.toUByte << n

  def expectedUbyteShl8: UByte =
    0.toUByte

  def ubyteShl128: UByte =
    val n: UByte = 128.toUByte
    1.toUByte << n

  def expectedUbyteShl128: UByte =
    0.toUByte

  def ubyteLshr8: UByte =
    val n: UByte = 8.toUByte
    255.toUByte >>> n

  def expectedUbyteLshr8: UByte =
    0.toUByte

  def ubyteLshr255: UByte =
    val n: UByte = 255.toUByte
    255.toUByte >>> n

  def expectedUbyteLshr255: UByte =
    0.toUByte

  // UShort

  def ushortShl15: UShort =
    val n: UShort = 15.toUShort
    1.toUShort << n

  def expectedUshortShl15: UShort =
    32768.toUShort

  def ushortLshr15: UShort =
    val n: UShort = 15.toUShort
    0x8000.toUShort >>> n

  def expectedUshortLshr15: UShort =
    1.toUShort

  def ushortShl16: UShort =
    val n: UShort = 16.toUShort
    1.toUShort << n

  def expectedUshortShl16: UShort =
    0.toUShort

  def ushortLshr16: UShort =
    val n: UShort = 16.toUShort
    65535.toUShort >>> n

  def expectedUshortLshr16: UShort =
    0.toUShort

  def ushortLshr65535: UShort =
    val n: UShort = 65535.toUShort
    65535.toUShort >>> n

  def expectedUshortLshr65535: UShort =
    0.toUShort

  // UInt: 0 for amounts of 32 or more, unlike Int

  def uintShl31: UInt =
    val n: UInt = 31.toUInt
    1.toUInt << n

  def expectedUintShl31: UInt =
    2147483648L.toUInt

  def uintLshr31: UInt =
    val n: UInt = 31.toUInt
    2147483648L.toUInt >>> n

  def expectedUintLshr31: UInt =
    1.toUInt

  def uintShl32: UInt =
    val n: UInt = 32.toUInt
    1.toUInt << n

  def expectedUintShl32: UInt =
    0.toUInt

  def uintShl33: UInt =
    val n: UInt = 33.toUInt
    1.toUInt << n // not 2 as for Int

  def expectedUintShl33: UInt =
    0.toUInt

  def uintLshr2Pow31: UInt =
    val n: UInt = 2147483648L.toUInt // negative as an Int
    4294967295L.toUInt >>> n

  def expectedUintLshr2Pow31: UInt =
    0.toUInt

  def uintLshrMax: UInt =
    val n: UInt = 4294967295L.toUInt
    4294967295L.toUInt >>> n

  def expectedUintLshrMax: UInt =
    0.toUInt

  // ULong: 0 for amounts of 64 or more, unlike Long

  def ulongShl62: ULong =
    val n: ULong = 62.toULong
    1.toULong << n

  def expectedUlongShl62: ULong =
    4611686018427387904L.toULong

  def ulongLshr63: ULong =
    val n: ULong = 63.toULong
    ULong.MaxValue >>> n

  def expectedUlongLshr63: ULong =
    1.toULong

  def ulongShl64: ULong =
    val n: ULong = 64.toULong
    1.toULong << n

  def expectedUlongShl64: ULong =
    0.toULong

  def ulongShl65: ULong =
    val n: ULong = 65.toULong
    1.toULong << n // not 2 as for Long

  def expectedUlongShl65: ULong =
    0.toULong

  def ulongLshrMax: ULong =
    val n: ULong = ULong.MaxValue
    ULong.MaxValue >>> n

  def expectedUlongLshrMax: ULong =
    0.toULong
