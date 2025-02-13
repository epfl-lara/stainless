/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object Array5 {

  def foo(a: Array[Int]): Int = {
    require(a.length > 0)
    val a2 = a.updated(1, 2)
    a2(0)
  }

}
