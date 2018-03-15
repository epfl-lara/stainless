/* Copyright 2009-2018 EPFL, Lausanne */

import stainless.lang._

object LetTest {
  def test(x:BigInt) = {
    require(x > 0)
    val i = x + 1
    i + x
  } ensuring { res => res > 1 }
}
