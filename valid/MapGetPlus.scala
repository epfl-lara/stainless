/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object MapGetPlus {
  def test1(a: Map[BigInt, BigInt]) = {
    require(!(a contains 0))
    val b = a + (0, 1)
    val c = a + (BigInt(0) -> BigInt(1))
    b(0) == c(0)
  }.holds

  def test2(a: Map[BigInt, BigInt]) = {
    require(!(a contains 0))
    val t = (BigInt(0) -> BigInt(1))
    val b = a + (0, 1)
    val c = a + t
    b(0) == c(0)
  }.holds
}
