/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object Array4 {

  def foo(a: Array[Int]): Int = {
    val tmp = a.updated(0, 0)
    tmp(0)
  }

}
