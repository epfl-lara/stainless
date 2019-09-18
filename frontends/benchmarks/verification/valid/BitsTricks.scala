/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.annotation._
import stainless.lang._

object BitsTricks {

  def bitAt(x: Int, n: Int): Boolean = {
    require(n >= 0 && n < 32)
    ((x >> n) & 1) == 1
  }

  def isEven(x: Int): Boolean = {
    (x & 1) == 0
  } ensuring(res => res == (x % 2 == 0))

  def isNegative(x: Int): Boolean = {
    (x >>> 31) == 1
  } ensuring(b => b == x < 0)

  def isBitNSet(x: Int, n: Int): Int = {
    require(n >= 0 && n < 32)
    (x & (1 << n))
  }

  def testBitSet1(): Int = {
    isBitNSet(122, 3)
  } ensuring(_ != 0)
  def testBitSet2(): Int = {
    isBitNSet(-33, 5)
  } ensuring(_ == 0)

  def setBitN(x: Int, n: Int): Int = {
    require(n >= 0 && n < 32)
    x | (1 << n)
  } ensuring(res => isBitNSet(res, n) != 0)

  def toggleBitN(x: Int, n: Int): Int = {
    require(n >= 0 && n < 32)
    x ^ (1 << n)
  } ensuring(res => 
      if(isBitNSet(x, n) != 0) isBitNSet(res, n) == 0
      else isBitNSet(res, n) != 0)

  def checkDoubleXor(x: Int, y: Int): Int = {
    x ^ y ^ x
  } ensuring(res => res == y)

}
