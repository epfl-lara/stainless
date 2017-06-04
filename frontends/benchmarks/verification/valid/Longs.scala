/* Copyright 2009-2017 EPFL, Lausanne */

import stainless.lang._

object Longs {
  def fun() = {
    val l = 8589934592L
    val m = 1073741824L
    l / m == 8
  }.holds

  def gun(i: Byte, j: Int): Long = {
    require(0 <= j && j < 32)
    i.toLong << j
  } ensuring { res =>
    pow2(j) * i == res
  }

  def pow2(y: Long): Long = {
    require(y >= 0)
    if (y == 0) 1
    else 2 * pow2(y - 1)
  }

  /** This tests the slot allocation in CodeGen:
   *  b should be at index a + 2.
   *  The JVM will reject the `.class` if any function
   *  if <static> is invalid; no need to call it.
   */
  def slots(a: Long, b: Int, c: Long): Long = {
    b
  }

}

