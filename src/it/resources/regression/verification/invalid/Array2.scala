/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object Array2 {

  def foo(a: Array[Int]): Int = {
    require(a.length > 2)
    a(2)
  } ensuring(_ == 0)

}
