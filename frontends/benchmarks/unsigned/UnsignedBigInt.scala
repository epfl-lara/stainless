/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.math.Unsigned._
import stainless.math.wrapping

/** Conversions of unsigned values to `BigInt`, which GenC does not support (see `UnsignedSemantics`). */
object UnsignedBigInt {

  def test1: BigInt = wrapping(200.toUByte.toBigInt)
  def test2: BigInt = wrapping(UShort.MaxValue.toBigInt)
  def test3: BigInt = wrapping(UInt.MaxValue.toBigInt)
  def test4: BigInt = wrapping(ULong.MaxValue.toBigInt)
  def test5: BigInt = wrapping((0.toUInt - 1.toUInt).toBigInt + 1)
  def test6: BigInt = wrapping((-1).toULong.toBigInt + 1)
  def test7: BigInt = wrapping(Long.MinValue.toULong.toBigInt)

  def checks(): Unit = {
    assert(test1 == BigInt(200))
    assert(test2 == BigInt(65535))
    assert(test3 == BigInt(4294967295L))
    assert(test4 == BigInt("18446744073709551615"))
    assert(test5 == BigInt(4294967296L))
    assert(test6 == BigInt("18446744073709551616"))
    assert(test7 == BigInt("9223372036854775808"))
  }

}
