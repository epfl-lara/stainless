/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object Array5 {

  def foo(a: Array[Int]): Int = {
    var i = 0
    var sum = 0
    (while(i < a.length) {
      sum = sum + a(i)
      i = i + 1
    }) invariant(i >= 0)
    sum
  }

  def bar(): Int = {
    val a = Array.fill(5)(5)
    foo(a)
  }

}
