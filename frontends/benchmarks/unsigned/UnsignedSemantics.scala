/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.annotation._
import stainless.io._
import stainless.math.Unsigned._
import stainless.math.wrapping

/** Semantics of the operations of `stainless.math.Unsigned`.
  *
  * Each `testN` computes a value and `UnsignedSemantics.check` lists the expected results.
  * `UnsignedSemanticsSuite` checks that these results are obtained when the program is:
  *  - verified by Stainless (the `checksN` functions assert them, so the solver has to agree),
  *  - evaluated by the recursive and by the code-generating evaluators,
  *  - compiled to C by GenC and run (`main` prints them, in the order of the `.check` file),
  *  - compiled by the Scala compiler and run on the JVM.
  *
  * Shifts by the size of the type or more, and divisions by zero, are only covered by `UnsignedJVMSuite`
  * and by the verification benchmarks, as they are undefined in C.
  *
  * The program verifies with `--strict-arithmetic`, as GenC requires: the wrap-arounds tested here are
  * intended, so every `testN` is in `wrapping` (they are defined in C for unsigned types, and GenC requires
  * the conversions to signed types to wrap around).
  */
object UnsignedSemantics {

  // Wrap-around
  def test1: UByte = wrapping(UByte.MaxValue + 1.toUByte)
  def test2: UByte = wrapping(0.toUByte - 1.toUByte)
  def test3: UByte = wrapping(200.toUByte * 3.toUByte)
  def test4: UShort = wrapping(60000.toUShort + 10000.toUShort)
  def test5: UInt = wrapping(UInt.MaxValue + 1.toUInt)
  def test6: UInt = wrapping(0.toUInt - 1.toUInt)
  def test7: UInt = wrapping(4000000000L.toUInt * 2.toUInt)
  def test8: ULong = wrapping(ULong.MaxValue + 1.toULong)
  def test9: ULong = wrapping(0.toULong - 1.toULong)

  // Division and remainder are unsigned
  def test10: UByte = wrapping(200.toUByte / 3.toUByte)
  def test11: UByte = wrapping(200.toUByte % 3.toUByte)
  def test12: UShort = wrapping(65535.toUShort / 2.toUShort)
  def test13: UInt = wrapping(UInt.MaxValue / 2.toUInt)
  def test14: UInt = wrapping(4000000000L.toUInt % 7.toUInt)
  def test15: ULong = wrapping(ULong.MaxValue / 3.toULong)
  def test16: ULong = wrapping(ULong.MaxValue % 10.toULong)

  // Unary operators
  def test17: UByte = wrapping(~0.toUByte)
  def test18: UByte = wrapping(-(1.toUByte))
  def test19: UShort = wrapping(~0x00FF.toUShort)
  def test20: UInt = wrapping(-(1.toUInt))
  def test21: ULong = wrapping(~0.toULong)

  // Comparisons are unsigned
  def test22: Boolean = wrapping(200.toUByte > 100.toUByte)
  def test23: Boolean = wrapping(40000.toUShort > 30000.toUShort)
  def test24: Boolean = wrapping(UInt.MaxValue > 1.toUInt)
  def test25: Boolean = wrapping(ULong.MaxValue > 1.toULong)
  def test26: Boolean = wrapping(255.toUByte >= 255.toUByte && 255.toUByte <= 255.toUByte)
  def test27: Boolean = wrapping(2147483648L.toUInt < 2147483647.toUInt)

  // Bitwise operators
  def test28: UByte = wrapping(0xF0.toUByte & 0x3C.toUByte)
  def test29: UByte = wrapping(0xF0.toUByte | 0x0F.toUByte)
  def test30: UByte = wrapping(0xAA.toUByte ^ 0xFF.toUByte)
  def test31: UInt = wrapping(0x0F0F0F0F.toUInt & 0x00FF00FF.toUInt)
  def test32: ULong = wrapping(ULong.MaxValue ^ 1.toULong)

  // Shifts by amounts smaller than the size (the only ones defined in C); `>>>` is a logical shift
  def test33: UByte = wrapping(0x0F.toUByte << 4.toUByte)
  def test34: UByte = wrapping(0xF0.toUByte >>> 4.toUByte)
  def test35: UByte = wrapping(0x81.toUByte << 1.toUByte)
  def test36: UShort = wrapping(0x8000.toUShort >>> 15.toUShort)
  def test37: UInt = wrapping(1.toUInt << 31.toUInt)
  def test38: UInt = wrapping(2147483648L.toUInt >>> 31.toUInt)
  def test39: ULong = wrapping(1.toULong << 63.toULong)
  def test40: ULong = wrapping(ULong.MaxValue >>> 63.toULong)
  def test41: ULong = wrapping(ULong.MaxValue >>> 60.toULong)

  // Conversions between unsigned types: zero-extension and truncation
  def test42: UShort = wrapping(200.toUByte.toUShort)
  def test43: ULong = wrapping(UInt.MaxValue.toULong)
  def test44: UInt = wrapping(0xFFFF.toUShort.toUInt)
  def test45: UByte = wrapping(0x1234.toUShort.toUByte)
  def test46: UShort = wrapping(0x12345678.toUInt.toUShort)
  def test47: UInt = wrapping(0x1FFFFFFFFL.toULong.toUInt)

  // Conversions to the signed types: zero-extension or truncation, then reinterpretation of the bits
  def test48: Byte = wrapping(200.toUByte.toByte)
  def test49: Int = wrapping(200.toUByte.toInt)
  def test50: Short = wrapping(0x8000.toUShort.toShort)
  def test51: Int = wrapping(0x8000.toUShort.toInt)
  def test52: Int = wrapping(UInt.MaxValue.toInt)
  def test53: Long = wrapping(UInt.MaxValue.toLong)
  def test54: Long = wrapping(ULong.MaxValue.toLong)
  def test55: Byte = wrapping(0x1FF.toUShort.toByte)

  // Conversions from the signed types: sign-extension or truncation, then reinterpretation of the bits
  def test56: UByte = wrapping((-56: Byte).toUByte)
  def test57: UInt = wrapping((-1).toUInt)
  def test58: UShort = wrapping((-2: Short).toUShort)
  def test59: ULong = wrapping(Long.MinValue.toULong)
  def test60: UShort = wrapping((-1: Byte).toUShort)
  def test61: UByte = wrapping(300.toUByte)
  def test62: ULong = wrapping((-1).toULong)

  // Nested operations wrap around at each step (in C, the operands of 8 and 16-bit operations are promoted to `int`)
  def test63: UByte = wrapping((200.toUByte + 100.toUByte) / 2.toUByte)
  def test64: Boolean = wrapping(200.toUByte + 100.toUByte < 200.toUByte)
  def test65: UShort = wrapping((60000.toUShort * 2.toUShort) >>> 8.toUShort)
  def test66: UShort = wrapping(60000.toUShort * 60000.toUShort)
  def test67: UByte = wrapping((0x81.toUByte << 1.toUByte) >>> 1.toUByte)
  def test68: UByte = wrapping((~0.toUByte) >>> 4.toUByte)
  def test69: UByte = wrapping((-1.toUByte) >>> 4.toUByte)
  def test70: UShort = wrapping((0.toUShort - 1.toUShort) / 2.toUShort)
  def test71: UInt = wrapping((200.toUByte + 100.toUByte).toUInt)

  // Arrays indexed by unsigned values
  def test72: Int = wrapping(Array(10, 20, 30, 40)(3.toUByte.toInt))
  def test73: Int = wrapping(Array(10, 20, 30, 40)(1.toULong.toInt))

  // The expected results, checked by the verifier.
  def checks1(): Unit = {
    assert(test1 == 0.toUByte)
    assert(test2 == 255.toUByte)
    assert(test3 == 88.toUByte)
    assert(test4 == 4464.toUShort)
    assert(test5 == 0.toUInt)
    assert(test6 == 4294967295L.toUInt)
    assert(test7 == 3705032704L.toUInt)
    assert(test8 == 0.toULong)
    assert(test9 == ULong.MaxValue)
    assert(test10 == 66.toUByte)
    assert(test11 == 2.toUByte)
    assert(test12 == 32767.toUShort)
    assert(test13 == 2147483647.toUInt)
    assert(test14 == 3.toUInt)
    assert(test15 == 6148914691236517205L.toULong)
    assert(test16 == 5.toULong)
    assert(test17 == 255.toUByte)
    assert(test18 == 255.toUByte)
    assert(test19 == 65280.toUShort)
    assert(test20 == 4294967295L.toUInt)
    assert(test21 == ULong.MaxValue)
    assert(test22)
  }

  def checks2(): Unit = {
    assert(test23)
    assert(test24)
    assert(test25)
    assert(test26)
    assert(!test27)
    assert(test28 == 48.toUByte)
    assert(test29 == 255.toUByte)
    assert(test30 == 85.toUByte)
    assert(test31 == 983055.toUInt)
    assert(test32 == BigInt("18446744073709551614").toULong)
    assert(test33 == 240.toUByte)
    assert(test34 == 15.toUByte)
    assert(test35 == 2.toUByte)
    assert(test36 == 1.toUShort)
    assert(test37 == 2147483648L.toUInt)
    assert(test38 == 1.toUInt)
    assert(test39 == BigInt("9223372036854775808").toULong)
    assert(test40 == 1.toULong)
    assert(test41 == 15.toULong)
    assert(test42 == 200.toUShort)
    assert(test43 == 4294967295L.toULong)
    assert(test44 == 65535.toUInt)
  }

  def checks3(): Unit = {
    assert(test45 == 52.toUByte)
    assert(test46 == 22136.toUShort)
    assert(test47 == 4294967295L.toUInt)
    assert(test48 == (-56: Byte))
    assert(test49 == 200)
    assert(test50 == (-32768: Short))
    assert(test51 == 32768)
    assert(test52 == -1)
    assert(test53 == 4294967295L)
    assert(test54 == -1L)
    assert(test55 == (-1: Byte))
    assert(test56 == 200.toUByte)
    assert(test57 == 4294967295L.toUInt)
    assert(test58 == 65534.toUShort)
    assert(test59 == BigInt("9223372036854775808").toULong)
    assert(test60 == 65535.toUShort)
    assert(test61 == 44.toUByte)
    assert(test62 == ULong.MaxValue)
    assert(test63 == 22.toUByte)
    assert(test64)
    assert(test65 == 212.toUShort)
    assert(test66 == 41984.toUShort)
  }

  def checks4(): Unit = {
    assert(test67 == 1.toUByte)
    assert(test68 == 15.toUByte)
    assert(test69 == 15.toUByte)
    assert(test70 == 32767.toUShort)
    assert(test71 == 44.toUInt)
    assert(test72 == 40)
    assert(test73 == 20)
  }

  // Printing helpers for `main`
  def printLong(x: Long)(implicit @ghost state: State): Unit = {
    if (x < 0) {
      StdOut.print("-")
      StdOut.printlnU64((~x).toULong + 1.toULong)
    } else {
      StdOut.printlnU64(x.toULong)
    }
  }
  def printBool(b: Boolean)(implicit @ghost state: State): Unit = StdOut.println(if (b) "true" else "false")

  // `main` prints the results in the order of the `.check` file. It is split into several functions
  // because the code-generating evaluator cannot compile a function with that many statements.
  def printResults1()(implicit @ghost state: State): Unit = {
    StdOut.printlnU8(test1)
    StdOut.printlnU8(test2)
    StdOut.printlnU8(test3)
    StdOut.printlnU16(test4)
    StdOut.printlnU32(test5)
    StdOut.printlnU32(test6)
    StdOut.printlnU32(test7)
    StdOut.printlnU64(test8)
    StdOut.printlnU64(test9)
    StdOut.printlnU8(test10)
    StdOut.printlnU8(test11)
    StdOut.printlnU16(test12)
    StdOut.printlnU32(test13)
    StdOut.printlnU32(test14)
    StdOut.printlnU64(test15)
    StdOut.printlnU64(test16)
    StdOut.printlnU8(test17)
    StdOut.printlnU8(test18)
    StdOut.printlnU16(test19)
    StdOut.printlnU32(test20)
    StdOut.printlnU64(test21)
    printBool(test22)
  }

  def printResults2()(implicit @ghost state: State): Unit = {
    printBool(test23)
    printBool(test24)
    printBool(test25)
    printBool(test26)
    printBool(test27)
    StdOut.printlnU8(test28)
    StdOut.printlnU8(test29)
    StdOut.printlnU8(test30)
    StdOut.printlnU32(test31)
    StdOut.printlnU64(test32)
    StdOut.printlnU8(test33)
    StdOut.printlnU8(test34)
    StdOut.printlnU8(test35)
    StdOut.printlnU16(test36)
    StdOut.printlnU32(test37)
    StdOut.printlnU32(test38)
    StdOut.printlnU64(test39)
    StdOut.printlnU64(test40)
    StdOut.printlnU64(test41)
    StdOut.printlnU16(test42)
    StdOut.printlnU64(test43)
    StdOut.printlnU32(test44)
  }

  def printResults3()(implicit @ghost state: State): Unit = {
    StdOut.printlnU8(test45)
    StdOut.printlnU16(test46)
    StdOut.printlnU32(test47)
    StdOut.println(test48.toInt)
    StdOut.println(test49)
    StdOut.println(test50.toInt)
    StdOut.println(test51)
    StdOut.println(test52)
    printLong(test53)
    printLong(test54)
    StdOut.println(test55.toInt)
    StdOut.printlnU8(test56)
    StdOut.printlnU32(test57)
    StdOut.printlnU16(test58)
    StdOut.printlnU64(test59)
    StdOut.printlnU16(test60)
    StdOut.printlnU8(test61)
    StdOut.printlnU64(test62)
    StdOut.printlnU8(test63)
    printBool(test64)
    StdOut.printlnU16(test65)
    StdOut.printlnU16(test66)
  }

  def printResults4()(implicit @ghost state: State): Unit = {
    StdOut.printlnU8(test67)
    StdOut.printlnU8(test68)
    StdOut.printlnU8(test69)
    StdOut.printlnU16(test70)
    StdOut.printlnU32(test71)
    StdOut.println(test72)
    StdOut.println(test73)
  }

  @cCode.`export`
  def main(): Unit = {
    @ghost implicit val state = newState
    printResults1()
    printResults2()
    printResults3()
    printResults4()
  }

}
