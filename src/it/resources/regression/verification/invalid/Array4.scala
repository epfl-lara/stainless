/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object Array4 {

  def foo(a: Array[Int]): Int = {
    val tmp = a.updated(0, 0)
    tmp(0)
  }

}
