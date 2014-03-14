/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._

object Array4 {

  def foo(a: Array[Int]): Int = {
    require(a.length > 2)
    a(2)
  } ensuring(_ == 0)

}
