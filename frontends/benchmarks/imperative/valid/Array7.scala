/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object Array7 {

  def foo(a: Array[Int]): Array[Int] = {
    require(a.length > 0)
    val a2 = Array.fill(a.length)(0)
    var i = 0
    (while(i < a.length) {
      decreases(a.length - i)
      a2(i) = a(i)
      i = i + 1
    }) invariant(a.length == a2.length && 0 <= i && i <= a.length && (if(i > 0) a2(0) == a(0) else true))
    a2
  }.ensuring(_(0) == a(0))

}
