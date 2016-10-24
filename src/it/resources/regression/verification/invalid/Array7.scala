/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object Array7 {

  def foo(a: Array[Int]): Int = {
    require(a.length > 0)
    val a2 = a.updated(1, 2)
    a2(0)
  }

}
