/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._

object Array5 {

  def foo(): Int = {
    val x = 10
    val a = Array(0,0,x,0,0)
    a(2)
  } ensuring(_ >= 0)

}
