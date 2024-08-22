/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object While3 {

  def foo(): Int = {
    var a = 0
    var i = 0
    (while({i = i+2; i <= 10}) {
      decreases(10 - i)
      a = a + i
      i = i - 1
    }).invariant(i >= 0)
    a
 }.ensuring(_ == 54)

}
