/* Copyright 2009-2021 EPFL, Lausanne */

package stainless.codegen.runtime

import java.math.BigInteger

final class BitVector(private val signed: Boolean, private val bits: Array[Boolean]) {

  def size = bits.length

  def this(signed: Boolean, bi: BigInteger, size: Int) = this(signed, BitVector.computeBits(signed, bi, size))

  def this(signed: Boolean, value: String, size: Int) = this(signed, new BigInteger(value), size)
  def this(value: Byte, size: Int)   = this(true, new BigInteger(value.toString), size)
  def this(value: Short, size: Int)  = this(true, new BigInteger(value.toString), size)
  def this(value: Int, size: Int)    = this(true, new BigInteger(value.toString), size)
  def this(value: Long, size: Int)   = this(true, new BigInteger(value.toString), size)

  def toBigInteger: BigInteger = {
    val two = new BigInteger("2")
    val unsigned = bits.reverse.zipWithIndex.foldLeft(BigInteger.ZERO) { case (res, (bit, i)) =>
      val bitValue = if (bit) two.pow(i) else BigInteger.ZERO
      res.add(bitValue)
    }
    if (signed && bits.head) unsigned.subtract(two.pow(size)) else unsigned
  }

  private def toUnsigned: BitVector = new BitVector(false, bits)

  def toByte: Byte = toBigInteger.byteValueExact
  def toShort: Short = toBigInteger.shortValueExact
  def toInt: Int = toBigInteger.intValueExact
  def toLong: Long = toBigInteger.longValueExact

  def add(that: BitVector): BitVector = {
    val (newBits, lastCarry) =
      (bits zip that.bits).foldRight[(List[Boolean], Boolean)]((Nil, false)) { case ((b1, b2), (res, carry)) =>
        val newBit = b1 ^ b2 ^ carry
        val newCarry = (b1 && b2) || (b1 && carry) || (b2 && carry)
        (newBit :: res) -> newCarry
      }
    new BitVector(signed, newBits.toArray)
  }

  def neg: BitVector = not.add(new BitVector(signed, "1", size)) // -x equals (~x)+1
  def sub(that: BitVector): BitVector = add(that.neg)
  def mult(that: BitVector): BitVector = new BitVector(signed, toBigInteger.multiply(that.toBigInteger), size)
  def div(that: BitVector): BitVector = new BitVector(signed, toBigInteger.divide(that.toBigInteger), size)
  def rem(that: BitVector): BitVector = new BitVector(signed, toBigInteger.remainder(that.toBigInteger), size)
  def mod(that: BitVector): BitVector = new BitVector(signed, {
    val (bi, tbi) = (toBigInteger, that.toBigInteger)
    if (tbi.compareTo(BigInteger.ZERO) < 0) bi.mod(tbi.negate)
    else bi.mod(tbi)
  }, size)

  def not: BitVector = new BitVector(signed, bits map (!_))
  def and(that: BitVector): BitVector = new BitVector(signed, (bits zip that.bits) map (p => p._1 && p._2))
  def or(that: BitVector): BitVector  = new BitVector(signed, (bits zip that.bits) map (p => p._1 || p._2))
  def xor(that: BitVector): BitVector = new BitVector(signed, (bits zip that.bits) map (p => p._1 ^  p._2))

  def shiftLeft(that: BitVector): BitVector = {
    val shift = (that.toUnsigned.toBigInteger min new BigInteger(size.toString)).intValueExact
    new BitVector(signed, toBigInteger.shiftLeft(shift), size)
  }

  def lShiftRight(that: BitVector): BitVector = {
    val shift = (that.toUnsigned.toBigInteger min new BigInteger(size.toString)).intValueExact
    val msbBits = (0 until shift) map { _ => bits.head }
    val remainings = bits.dropRight(shift).toSeq
    val newBits = msbBits ++ remainings
    assert(newBits.length == size)
    new BitVector(signed, newBits.toArray)
  }

  // Preserve MSB (sign bit)
  def aShiftRight(that: BitVector): BitVector = {
    val shift = (that.toUnsigned.toBigInteger min new BigInteger(size.toString)).intValueExact
    new BitVector(signed, toBigInteger.shiftRight(shift), size)
  }

  // Apply sign extension when growing, simply drop bits when shrinking
  def cast(newSize: Int): BitVector = {
    val newBits: Seq[Boolean] =
      if (newSize > size) ((size to newSize) map { _ => bits.head }) ++ bits
      else bits.toIndexedSeq.drop(size - newSize)
    new BitVector(signed, newBits.toArray)
  }

  def lessThan(that: BitVector): Boolean = toBigInteger.compareTo(that.toBigInteger) < 0
  def lessEquals(that: BitVector): Boolean = toBigInteger.compareTo(that.toBigInteger) <= 0
  def greaterThan(that: BitVector): Boolean = toBigInteger.compareTo(that.toBigInteger) > 0
  def greaterEquals(that: BitVector): Boolean = toBigInteger.compareTo(that.toBigInteger) >= 0

  override def equals(that: Any): Boolean = that match {
    // the conversion to Seq is mandatory! Array.equals doesn't work as one expect.
    case that: BitVector => signed == that.signed && bits.toSeq == that.bits.toSeq
    case _ => false
  }

  override def hashCode: Int = (signed, bits.toSeq).hashCode

  override def toString: String =
    (if (signed) "" else "u") +
    bits.map(b => if (b) "1" else "0").mkString("")
}

object BitVector {
  private def computeBits(signed: Boolean, bi: BigInteger, size: Int): Array[Boolean] = {
    // Extract positive numbers only
    def extract(bi: BigInteger): Array[Boolean] = {
      val two = new BigInteger("2")
      (0 until size).map { i => bi.and(two.pow(i)).compareTo(BigInteger.ZERO) > 0 }.reverse.toArray
    }

    if (bi.compareTo(BigInteger.ZERO) >= 0) {
      extract(bi)
    } else if (!signed) {
      new BitVector(signed, new BigInteger("2").pow(size).add(bi), size).bits
    } else {
      new BitVector(signed, bi.negate, size).neg.bits
    }
  }
}
