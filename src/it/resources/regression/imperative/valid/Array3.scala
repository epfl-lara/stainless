/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object Array3 {

  def foo(): Int = {
    val a = Array.fill(5)(3)
    var i = 0
    var sum = 0
    (while(i < a.length) {
      sum = sum + a(i)
      i = i + 1
    }) invariant(i >= 0)
    sum
  } ensuring(_ == 15)

}
