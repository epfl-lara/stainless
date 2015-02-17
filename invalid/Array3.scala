/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._

object Test {

  def find(c: Array[Int], i: Int): Int = {
    require(i >= 0)
    if(c(i) == i)
      42
    else
      12
  } ensuring(_ > 0)

}
