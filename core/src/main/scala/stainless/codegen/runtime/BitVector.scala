/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.codegen.runtime

import java.math.BigInteger

final class BitVector(private val bits: Array[Boolean]) {

  /*private*/ def this(bi: BigInteger, size: Int) = this({
    def extract(bi: BigInteger): Array[Boolean] = {
      val two = new BigInteger("2")
      (0 until size).map { i => bi.and(two.pow(i)).compareTo(BigInteger.ZERO) > 0 }.toArray
    }

    if (bi.compareTo(BigInteger.ZERO) >= 0) {
      extract(bi)
    } else {
      val nres = extract(bi.negate)
      (0 until size).foldLeft[(List[Boolean], Boolean)]((Nil, false)) { case ((res, seen1), i) =>
        if ((nres(i) && !seen1) || (!nres(i) && seen1)) (true :: res, true) else (false :: res, seen1)
      }._1.reverse.toArray
    }
  })
  
  private def toBigInteger: BigInteger = {
    val two = new BigInteger("2")
    val res = bits.zipWithIndex.foldLeft(BigInteger.ZERO) {
      case (res, (b, i)) => if (b) res.add(two.pow(i)) else res
    }
    if (bits.last) res.subtract(two.pow(bits.length)) else res
  }

  def add(that: BitVector): BitVector = new BitVector(
    (0 until bits.length).foldLeft[(List[Boolean], Boolean)]((Nil, false)) { case ((res, carry), i) =>
      val (b1, b2) = (bits(i), that.bits(i))
      ((b1 ^ b2 ^ carry) :: res, (b1 && b2) || (b1 && carry) || (b2 && carry))
    }._1.reverse.toArray)

  def sub(that: BitVector): BitVector = new BitVector(toBigInteger.subtract(that.toBigInteger), bits.length)
  def mult(that: BitVector): BitVector = new BitVector(toBigInteger.multiply(that.toBigInteger), bits.length)
  def div(that: BitVector): BitVector = new BitVector(toBigInteger.divide(that.toBigInteger), bits.length)
  def rem(that: BitVector): BitVector = new BitVector(toBigInteger.remainder(that.toBigInteger), bits.length)
  def mod(that: BitVector): BitVector = new BitVector({
    val (bi, tbi) = (toBigInteger, that.toBigInteger)
    if (tbi.compareTo(BigInteger.ZERO) < 0) bi.mod(tbi.negate)
    else bi.mod(tbi)
  }, bits.length)

  def neg: BitVector = new BitVector(toBigInteger.negate, bits.length)

  def lessThan(that: BitVector): Boolean = toBigInteger.compareTo(that.toBigInteger) < 0
  def lessEquals(that: BitVector): Boolean = toBigInteger.compareTo(that.toBigInteger) <= 0
  def greaterThan(that: BitVector): Boolean = toBigInteger.compareTo(that.toBigInteger) > 0
  def greaterEquals(that: BitVector): Boolean = toBigInteger.compareTo(that.toBigInteger) >= 0

  def and(that: BitVector): BitVector = new BitVector((bits zip that.bits).map(p => p._1 && p._2))
  def or(that: BitVector): BitVector = new BitVector((bits zip that.bits).map(p => p._1 || p._2))
  def xor(that: BitVector): BitVector = new BitVector((bits zip that.bits).map(p => p._1 ^ p._2))

  def not: BitVector = new BitVector(bits.map(!_))

  def shiftLeft(that: BitVector): BitVector = new BitVector({
    val count = that.toBigInteger.intValue
    (0 until bits.length).map(i => if (i < count) false else bits(i - count)).toArray
  })

  def lShiftRight(that: BitVector): BitVector = new BitVector({
    val count = that.toBigInteger.intValue
    (0 until bits.length).map(i => if (i + count >= bits.length) false else bits(i + count)).toArray
  })

  def aShiftRight(that: BitVector): BitVector = new BitVector({
    val count = that.toBigInteger.intValue
    lazy val last = bits.last
    (0 until bits.length).map(i => if (i + count >= bits.length) last else bits(i + count)).toArray
  })

  override def equals(that: Any): Boolean = that match {
    case bv: BitVector => bits == bv.bits
    case _ => false
  }

  override def hashCode: Int = bits.hashCode

  override def toString: String = bits.map(b => if (b) "1" else "0").mkString("")
}

