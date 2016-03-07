/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object ArrayUpdated {

  def test(a: Array[Int]): Int = {
    require(a.length > 0)
    val a2 = a.updated(0, 2)
    a2(0)
  } ensuring(res => res == 2)

}
