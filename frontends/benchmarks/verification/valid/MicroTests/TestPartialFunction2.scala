/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._

object TestPartialFunctions2 {
  def partial(x: BigInt, y: BigInt): BigInt = {
    require(x > y)
    x - y
  } ensuring (_ >= BigInt(0))

  def test(x: BigInt): Boolean = {
    require(x > 0)
    val f = PartialFunction(partial _)
    assert(!f.pre(0, 0))
    f(x, 0) > 0
  }.holds
}
