/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object Array3 {
  def find(c: Array[Int], i: Int): Int = {
    require(i >= 0)
    if(c(i) == i)
      42
    else
      12
  } ensuring(_ > 0)

}
