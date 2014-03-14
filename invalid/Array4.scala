/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._

object Array4 {

  def foo(a: Array[Int]): Int = {
    val tmp = a.updated(0, 0)
    42
  }

}
