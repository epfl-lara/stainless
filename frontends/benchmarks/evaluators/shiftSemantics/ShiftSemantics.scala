/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.math.Unsigned._

/** On the JVM, the amount of `Int` and `Long` shifts is taken modulo the width (`1 << 33 == 2`), and a
  * negative amount is read modulo the width too (`1 << -1 == Int.MinValue`), whereas shifting a
  * `stainless.math.Unsigned` value by the size of its type or more gives 0, as in SMT-LIB. Both evaluators
  * must agree, see https://github.com/epfl-lara/stainless/issues/1828.
  *
  * The amounts are bound to `val`s so that the Scala compiler does not fold the shifts itself.
  */
object ShiftSemantics {

  def shl31: Int = { val n = 31; 1 << n }
  def expectedShl31: Int = -2147483648

  def shl33: Int = { val n = 33; 1 << n }
  def expectedShl33: Int = 2

  def shlNegative: Int = { val n = -1; 1 << n }
  def expectedShlNegative: Int = -2147483648

  def shlMinValueNegative: Int = { val n = -1; -2147483648 << n }
  def expectedShlMinValueNegative: Int = 0

  def ashr32: Int = { val n = 32; -2147483648 >> n }
  def expectedAshr32: Int = -2147483648

  def ashr33: Int = { val n = 33; -2147483648 >> n }
  def expectedAshr33: Int = -1073741824

  def ashrNegative: Int = { val n = -1; -2147483648 >> n }
  def expectedAshrNegative: Int = -1

  def lshr33: Int = { val n = 33; -2147483648 >>> n }
  def expectedLshr33: Int = 1073741824

  def lshrNegative: Int = { val n = -1; -1 >>> n }
  def expectedLshrNegative: Int = 1

  def longShl65: Long = { val n = 65; 1L << n }
  def expectedLongShl65: Long = 2L

  def longShlNegative: Long = { val n = -1; 1L << n }
  def expectedLongShlNegative: Long = -9223372036854775808L

  def longAshr64: Long = { val n = 64; -9223372036854775808L >> n }
  def expectedLongAshr64: Long = -9223372036854775808L

  def longAshr65: Long = { val n = 65; -9223372036854775808L >> n }
  def expectedLongAshr65: Long = -4611686018427387904L

  def longLshr65: Long = { val n = 65; -9223372036854775808L >>> n }
  def expectedLongLshr65: Long = 4611686018427387904L

  def longShlLongAmount: Long = { val n = 4294967361L; 1L << n } // 2^32 + 65
  def expectedLongShlLongAmount: Long = 2L

  def ubyteShl8: Boolean = { val n = 8.toUByte; (1.toUByte << n) == 0.toUByte }
  def ushortLshr16: Boolean = { val n = 16.toUShort; (UShort.MaxValue >>> n) == 0.toUShort }
  def uintShl31: Boolean = { val n = 31.toUInt; (1.toUInt << n) == 2147483648L.toUInt }
  def uintShl32: Boolean = { val n = 32.toUInt; (1.toUInt << n) == 0.toUInt }
  def uintShl33: Boolean = { val n = 33.toUInt; (1.toUInt << n) == 0.toUInt } // not 2 as for `Int`
  def uintLshrMax: Boolean = { val n = UInt.MaxValue; (UInt.MaxValue >>> n) == 0.toUInt }
  def ulongShl65: Boolean = { val n = 65.toULong; (1.toULong << n) == 0.toULong }
  def ulongLshrMax: Boolean = { val n = ULong.MaxValue; (ULong.MaxValue >>> n) == 0.toULong }
  def expectedTrue: Boolean = true

}
