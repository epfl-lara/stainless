/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._

object ArrayUpdated {

  def test(a: Array[Int]): Int = {
    require(a.length > 0)
    val a2 = a.updated(0, 2)
    a2(0)
  } ensuring(res => res == 2)

  def testBigInt(a: Array[BigInt]): BigInt = {
    require(a.length > 0)
    val a2 = a.updated(0, BigInt(2))
    a2(0)
  } ensuring(res => res == 2)

}
