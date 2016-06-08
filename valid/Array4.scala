/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object Array4 {

  def foo(x: Int): Int = {
    require(x >= 0)
    val a = Array(0,0,x,0,0)
    a(2)
  } ensuring(_ >= 0)

}
