/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.codegen.runtime

import java.math.BigInteger

final class BitVector(private val bits: Array[Boolean]) {

  def size = bits.length

  def this(bi: BigInteger, size: Int) = this({
    // Extract positive numbers only
    def extract(bi: BigInteger): Array[Boolean] = {
      val two = new BigInteger("2")
      (0 until size).map { i => bi.and(two.pow(i)).compareTo(BigInteger.ZERO) > 0 }.reverse.toArray
    }

    if (bi.compareTo(BigInteger.ZERO) >= 0) {
      extract(bi)
    } else {
      new BitVector(bi.negate, size).neg.bits
    }
  })

  def this(value: String, size: Int) = this(new BigInteger(value), size)
  def this(value: Byte, size: Int)   = this(new BigInteger(value.toString), size)
  def this(value: Short, size: Int)  = this(new BigInteger(value.toString), size)
  def this(value: Int, size: Int)    = this(new BigInteger(value.toString), size)
  def this(value: Long, size: Int)   = this(new BigInteger(value.toString), size)

  def toBigInteger: BigInteger = {
    val two = new BigInteger("2")
    val unsigned = bits.reverse.zipWithIndex.foldLeft(BigInteger.ZERO) { case (res, (bit, i)) =>
      val bitValue = if (bit) two.pow(i) else BigInteger.ZERO
      res.add(bitValue)
    }
    if (bits.head) unsigned.subtract(two.pow(size)) else unsigned
  }

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
    new BitVector(newBits.toArray)
  }

  def neg: BitVector = this.not.add(new BitVector("1", size)) // -x equals (~x)+1
  def sub(that: BitVector): BitVector = this.add(that.neg)
  def mult(that: BitVector): BitVector = new BitVector(this.toBigInteger.multiply(that.toBigInteger), size)
  def div(that: BitVector): BitVector = new BitVector(this.toBigInteger.divide(that.toBigInteger), size)
  def rem(that: BitVector): BitVector = new BitVector(this.toBigInteger.remainder(that.toBigInteger), size)
  def mod(that: BitVector): BitVector = new BitVector({
    val (bi, tbi) = (this.toBigInteger, that.toBigInteger)
    if (tbi.compareTo(BigInteger.ZERO) < 0) bi.mod(tbi.negate)
    else bi.mod(tbi)
  }, bits.length)

  def not: BitVector = new BitVector(bits map { !_ })
  def and(that: BitVector): BitVector = new BitVector((bits zip that.bits) map { case (b1, b2) => b1 && b2 })
  def or(that: BitVector): BitVector  = new BitVector((bits zip that.bits) map { case (b1, b2) => b1 || b2 })
  def xor(that: BitVector): BitVector = new BitVector((bits zip that.bits) map { case (b1, b2) => b1 ^  b2 })

  def shiftLeft(that: BitVector): BitVector = if (that.isNegative) ??? /* negative shift means what exactly? */ else {
    val shift = that.toBigInteger.intValueExact()
    new BitVector(this.toBigInteger.shiftLeft(shift), size)
  }

  def lShiftRight(that: BitVector): BitVector = if (that.isNegative) ??? /* negative shift means what exactly? */ else {
    val shift = math.min(size, that.toBigInteger.intValueExact)
    val msbBits = (0 until shift) map { _ => bits.head }
    val remainings = bits.dropRight(shift).toSeq
    val newBits = msbBits ++ remainings
    assert(newBits.length == size)
    new BitVector(newBits.toArray)
  }

  // Preserve MSB (sign bit)
  def aShiftRight(that: BitVector): BitVector = if (that.isNegative) ??? /* negative shift means what exactly? */ else {
    val shift = that.toBigInteger.intValueExact()
    new BitVector(this.toBigInteger.shiftRight(shift), size)
  }

  // Apply sign extension when growing, simply drop bits when shrinking
  def cast(newSize: Int): BitVector = {
    val newBits: Seq[Boolean] =
      if (newSize > size) ((size to newSize) map { _ => bits.head }) ++ bits
      else bits.drop(size - newSize)
    new BitVector(newBits.toArray)
  }

  def lessThan(that: BitVector): Boolean = toBigInteger.compareTo(that.toBigInteger) < 0
  def lessEquals(that: BitVector): Boolean = toBigInteger.compareTo(that.toBigInteger) <= 0
  def greaterThan(that: BitVector): Boolean = toBigInteger.compareTo(that.toBigInteger) > 0
  def greaterEquals(that: BitVector): Boolean = toBigInteger.compareTo(that.toBigInteger) >= 0

  private def isNegative = toBigInteger.signum == -1

  override def equals(that: Any): Boolean = that match {
    case that: BitVector => this.bits.toSeq == that.bits.toSeq // the conversion to Seq is mandatory! Array.equals doesn't work as one expect.
    case _ => false
  }

  override def hashCode: Int = bits.hashCode

  override def toString: String = bits.map(b => if (b) "1" else "0").mkString("")
}

