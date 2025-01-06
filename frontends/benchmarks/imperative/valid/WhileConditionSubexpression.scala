/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._
import stainless.collection._
import stainless._

import stainless.lang._

object WhileConditionSubexpression {

  def test(x: Int): Boolean = {
    var b = false
    var i = 0
    (while(!b && i < 10) {
      decreases(10 - i)
      if(i == x)
        b = true
      i += 1
    }).invariant(i >= 0)
    b
 }.ensuring(res => res || (x != 0 && x != 1 && x != 2))

}
