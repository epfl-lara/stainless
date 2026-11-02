/* Copyright 2009-2021 EPFL, Lausanne */

package stainless

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import stainless.math.Unsigned._

/** Unit tests of the executable (JVM) implementation of `stainless.math.Unsigned`.
  *
  * The semantics tested here is the one used by Stainless for verification (see the documentation of
  * `Unsigned`). `UnsignedSemanticsSuite` (integration tests) checks that the verifier, the evaluators,
  * GenC and the JVM agree on the `frontends/benchmarks/unsigned` programs; the cases below additionally
  * cover divisions by zero (which throw) and operations that are undefined in C (shifts by the size or more).
  *
  * The expected values are written as literals of the unsigned types: on the JVM, comparing an unsigned
  * value with an `Int` would compare it with the signed representation of the value.
  */
class UnsignedJVMSuite extends AnyFunSuite with Matchers {

  test("literals are converted from Int, Long and BigInt literals") {
    255.toUByte.toInt shouldBe 255
    65535.toUShort.toInt shouldBe 65535
    4294967295L.toUInt.toLong shouldBe 4294967295L
    Long.MaxValue.toULong.toLong shouldBe Long.MaxValue
    BigInt("18446744073709551615").toULong shouldBe ULong.MaxValue
    // Out of the range of the type: truncation, and reinterpretation of negative values
    256.toUByte shouldBe 0.toUByte
    (-1).toUByte shouldBe UByte.MaxValue
    65536.toUShort shouldBe 0.toUShort
    4294967296L.toUInt shouldBe 0.toUInt
    (-1).toULong shouldBe ULong.MaxValue
    // There are no implicit conversions
    assertDoesNotCompile("val b: UByte = 200")
  }

  test("conversions from BigInt are taken modulo 2^N") {
    BigInt(255).toUByte shouldBe UByte.MaxValue
    BigInt(65535).toUShort shouldBe UShort.MaxValue
    BigInt("4294967295").toUInt shouldBe UInt.MaxValue
    BigInt(0).toULong shouldBe 0.toULong
    BigInt(256).toUByte shouldBe 0.toUByte
    BigInt(-1).toUByte shouldBe UByte.MaxValue
    BigInt("18446744073709551616").toULong shouldBe 0.toULong
    BigInt(-1).toULong shouldBe ULong.MaxValue
  }

  test("minimum and maximum values") {
    UByte.MinValue.toStringUnsigned shouldBe "0"
    UByte.MaxValue.toStringUnsigned shouldBe "255"
    UShort.MinValue.toStringUnsigned shouldBe "0"
    UShort.MaxValue.toStringUnsigned shouldBe "65535"
    UInt.MinValue.toStringUnsigned shouldBe "0"
    UInt.MaxValue.toStringUnsigned shouldBe "4294967295"
    ULong.MinValue.toStringUnsigned shouldBe "0"
    ULong.MaxValue.toStringUnsigned shouldBe "18446744073709551615"
  }

  test("arithmetic wraps around") {
    UByte.MaxValue + 1.toUByte shouldBe 0.toUByte
    0.toUByte - 1.toUByte shouldBe UByte.MaxValue
    200.toUByte * 3.toUByte shouldBe 88.toUByte
    60000.toUShort + 10000.toUShort shouldBe 4464.toUShort
    0.toUShort - 1.toUShort shouldBe UShort.MaxValue
    UInt.MaxValue + 1.toUInt shouldBe 0.toUInt
    4000000000L.toUInt * 2.toUInt shouldBe 3705032704L.toUInt
    ULong.MaxValue + 1.toULong shouldBe 0.toULong
    0.toULong - 1.toULong shouldBe ULong.MaxValue
    -(1.toUByte) shouldBe UByte.MaxValue
    -(1.toUShort) shouldBe UShort.MaxValue
    -(1.toUInt) shouldBe UInt.MaxValue
    -(1.toULong) shouldBe ULong.MaxValue
    -(0.toUByte) shouldBe 0.toUByte
    ~0.toUByte shouldBe UByte.MaxValue
    ~0x00FF.toUShort shouldBe 65280.toUShort
    ~0.toUInt shouldBe UInt.MaxValue
    ~0.toULong shouldBe ULong.MaxValue
  }

  test("division and remainder are unsigned") {
    200.toUByte / 3.toUByte shouldBe 66.toUByte
    200.toUByte % 3.toUByte shouldBe 2.toUByte
    UByte.MaxValue / UByte.MaxValue shouldBe 1.toUByte
    65535.toUShort / 2.toUShort shouldBe 32767.toUShort
    65535.toUShort % 10.toUShort shouldBe 5.toUShort
    UInt.MaxValue / 2.toUInt shouldBe 2147483647.toUInt
    4000000000L.toUInt % 7.toUInt shouldBe 3.toUInt
    UInt.MaxValue / UInt.MaxValue shouldBe 1.toUInt
    ULong.MaxValue / 3.toULong shouldBe 6148914691236517205L.toULong
    ULong.MaxValue % 10.toULong shouldBe 5.toULong
    ULong.MaxValue / ULong.MaxValue shouldBe 1.toULong
  }

  test("division and remainder by zero throw") {
    an[ArithmeticException] should be thrownBy 1.toUByte / 0.toUByte
    an[ArithmeticException] should be thrownBy 1.toUByte % 0.toUByte
    an[ArithmeticException] should be thrownBy 1.toUShort / 0.toUShort
    an[ArithmeticException] should be thrownBy 1.toUShort % 0.toUShort
    an[ArithmeticException] should be thrownBy 1.toUInt / 0.toUInt
    an[ArithmeticException] should be thrownBy 1.toUInt % 0.toUInt
    an[ArithmeticException] should be thrownBy 1.toULong / 0.toULong
    an[ArithmeticException] should be thrownBy 1.toULong % 0.toULong
  }

  test("comparisons are unsigned") {
    (200.toUByte > 100.toUByte) shouldBe true
    (200.toUByte < 100.toUByte) shouldBe false
    (128.toUByte > 127.toUByte) shouldBe true
    (40000.toUShort > 30000.toUShort) shouldBe true
    (32768.toUShort >= 32767.toUShort) shouldBe true
    (2147483648L.toUInt > 2147483647.toUInt) shouldBe true
    (2147483648L.toUInt <= 2147483647.toUInt) shouldBe false
    (UInt.MaxValue > 1.toUInt) shouldBe true
    (ULong.MaxValue > 1.toULong) shouldBe true
    (Long.MinValue.toULong > Long.MaxValue.toULong) shouldBe true
    (255.toUByte >= 255.toUByte && 255.toUByte <= 255.toUByte) shouldBe true
    (0.toULong < 0.toULong) shouldBe false
  }

  test("bitwise operators") {
    0xF0.toUByte & 0x3C.toUByte shouldBe 48.toUByte
    0xF0.toUByte | 0x0F.toUByte shouldBe 255.toUByte
    0xAA.toUByte ^ 0xFF.toUByte shouldBe 85.toUByte
    0xFF00.toUShort | 0x00FF.toUShort shouldBe UShort.MaxValue
    0x0F0F0F0F.toUInt & 0x00FF00FF.toUInt shouldBe 983055.toUInt
    ULong.MaxValue ^ 1.toULong shouldBe ULong.MaxValue - 1.toULong
  }

  test("shifts by amounts smaller than the size") {
    0x0F.toUByte << 4.toUByte shouldBe 240.toUByte
    0x81.toUByte << 1.toUByte shouldBe 2.toUByte
    0xF0.toUByte >>> 4.toUByte shouldBe 15.toUByte
    0x80.toUByte >>> 7.toUByte shouldBe 1.toUByte
    0x8000.toUShort >>> 15.toUShort shouldBe 1.toUShort
    1.toUInt << 31.toUInt shouldBe 2147483648L.toUInt
    2147483648L.toUInt >>> 31.toUInt shouldBe 1.toUInt
    1.toULong << 63.toULong shouldBe Long.MinValue.toULong
    ULong.MaxValue >>> 63.toULong shouldBe 1.toULong
  }

  test("there is no `>>` (use `>>>`)") {
    assertDoesNotCompile("0xF0.toUByte >> 4.toUByte")
    assertDoesNotCompile("UInt.MaxValue >> 1.toUInt")
    assertCompiles("0xF0.toUByte >>> 4.toUByte")
  }

  test("shifting by the size or more yields 0 (the amount is read as an unsigned value)") {
    1.toUByte << 8.toUByte shouldBe 0.toUByte
    UByte.MaxValue >>> 8.toUByte shouldBe 0.toUByte
    UByte.MaxValue >>> UByte.MaxValue shouldBe 0.toUByte
    1.toUByte << 128.toUByte shouldBe 0.toUByte
    1.toUShort << 16.toUShort shouldBe 0.toUShort
    UShort.MaxValue >>> UShort.MaxValue shouldBe 0.toUShort
    1.toUInt << 32.toUInt shouldBe 0.toUInt
    1.toUInt << 33.toUInt shouldBe 0.toUInt // not `1 << (33 % 32)` as for `Int`
    UInt.MaxValue >>> UInt.MaxValue shouldBe 0.toUInt
    UInt.MaxValue >>> 2147483648L.toUInt shouldBe 0.toUInt
    1.toULong << 64.toULong shouldBe 0.toULong
    1.toULong << 65.toULong shouldBe 0.toULong
    ULong.MaxValue >>> ULong.MaxValue shouldBe 0.toULong
    ULong.MaxValue >>> Long.MinValue.toULong shouldBe 0.toULong
  }

  test("conversions between unsigned types: zero-extension and truncation") {
    200.toUByte.toUShort shouldBe 200.toUShort
    200.toUByte.toUInt shouldBe 200.toUInt
    200.toUByte.toULong shouldBe 200.toULong
    UShort.MaxValue.toUInt shouldBe 65535.toUInt
    UInt.MaxValue.toULong shouldBe 4294967295L.toULong
    0x1234.toUShort.toUByte shouldBe 0x34.toUByte
    0x12345678.toUInt.toUShort shouldBe 0x5678.toUShort
    0x12345678.toUInt.toUByte shouldBe 0x78.toUByte
    ULong.MaxValue.toUInt shouldBe UInt.MaxValue
    0x100000001L.toULong.toUInt shouldBe 1.toUInt
  }

  test("conversions to the signed types: zero-extension or truncation, then reinterpretation") {
    200.toUByte.toByte shouldBe (-56: Byte)
    200.toUByte.toShort shouldBe (200: Short)
    200.toUByte.toInt shouldBe 200
    200.toUByte.toLong shouldBe 200L
    0x8000.toUShort.toShort shouldBe Short.MinValue
    0x8000.toUShort.toInt shouldBe 32768
    0x1FF.toUShort.toByte shouldBe (-1: Byte)
    UInt.MaxValue.toInt shouldBe -1
    UInt.MaxValue.toLong shouldBe 4294967295L
    UInt.MaxValue.toShort shouldBe (-1: Short)
    ULong.MaxValue.toLong shouldBe -1L
    ULong.MaxValue.toInt shouldBe -1
    0x80000000L.toULong.toInt shouldBe Int.MinValue
  }

  test("conversions from the signed types: sign-extension or truncation, then reinterpretation") {
    (-56: Byte).toUByte shouldBe 200.toUByte
    (-1: Byte).toUShort shouldBe UShort.MaxValue
    (-1: Byte).toUInt shouldBe UInt.MaxValue
    (-1: Byte).toULong shouldBe ULong.MaxValue
    (127: Byte).toULong shouldBe 127.toULong
    (-2: Short).toUShort shouldBe 65534.toUShort
    (-2: Short).toUByte shouldBe 254.toUByte
    (-1).toUInt shouldBe UInt.MaxValue
    (-1).toULong shouldBe ULong.MaxValue
    300.toUByte shouldBe 44.toUByte
    70000.toUShort shouldBe 4464.toUShort
    Long.MinValue.toULong shouldBe Long.MaxValue.toULong + 1.toULong
    0x1FFFFFFFFL.toUInt shouldBe UInt.MaxValue
  }

  test("conversions to BigInt and to strings give the unsigned value") {
    200.toUByte.toBigInt shouldBe BigInt(200)
    UShort.MaxValue.toBigInt shouldBe BigInt(65535)
    UInt.MaxValue.toBigInt shouldBe BigInt(4294967295L)
    ULong.MaxValue.toBigInt shouldBe BigInt("18446744073709551615")
    Long.MinValue.toULong.toBigInt shouldBe BigInt("9223372036854775808")
    0.toULong.toBigInt shouldBe BigInt(0)
    200.toUByte.toStringUnsigned shouldBe "200"
    UInt.MaxValue.toStringUnsigned shouldBe "4294967295"
    // On the JVM, `toString` shows the signed representation of the value (see the documentation)
    200.toUByte.toString shouldBe "-56"
  }

  test("equality and hashing are those of the underlying bits") {
    (200.toUByte == 200.toUByte) shouldBe true
    (200.toUByte == 201.toUByte) shouldBe false
    (200.toUByte != 201.toUByte) shouldBe true
    (UInt.MaxValue == (-1).toUInt) shouldBe true
    Set[UByte](1.toUByte, 2.toUByte, 2.toUByte, 200.toUByte).size shouldBe 3
    Set[ULong](ULong.MaxValue, (-1).toULong).size shouldBe 1
  }

  test("arrays of unsigned values") {
    val a: Array[UByte] = Array(1.toUByte, 2.toUByte, 255.toUByte)
    a.length shouldBe 3
    a(2) shouldBe UByte.MaxValue
    a(2) = 7.toUByte
    (a(0) + a(1) + a(2)) shouldBe 10.toUByte
    Array(10, 20, 30, 40)(3.toUByte.toInt) shouldBe 40
  }
}
