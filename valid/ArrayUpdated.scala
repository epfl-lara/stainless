/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._

object Test {

  def test(a: Array[Int]): Int = {
    require(a.length > 0)
    val a2 = a.updated(0, 2)
    a2(0)
  } ensuring(res => res == 2)

}
