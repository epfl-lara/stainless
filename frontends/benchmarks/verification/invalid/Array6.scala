/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object Array6 {

  def foo(a: Array[Int]): Int = {
    require(a.length > 2)
    a(2)
  } ensuring(_ == 0)

}
