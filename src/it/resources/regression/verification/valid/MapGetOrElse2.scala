/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object MapGetOrElse2 {
  def test1(a: Map[BigInt, BigInt]) = {
    require(!(a contains 0))
    a.get(0)
  } ensuring {
    _ == None[BigInt]()
  }

  def test2(a: Map[BigInt, BigInt]) = {
    require(!(a contains 0))
    a.getOrElse(0, 0)
  } ensuring {
    _ == 0
  }
}
