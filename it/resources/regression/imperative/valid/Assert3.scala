/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object Assert3 {

  def test(i: Int): Int = {
    var j = i

    assert(j == i)
    j += 1
    assert(j == i + 1)
    j += 2
    assert(j == i + 3)

    j

  }

}
