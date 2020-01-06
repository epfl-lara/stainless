/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._

object Numeric {

  def max(x: BigInt, y: BigInt) = if (x > y) x else y

  def f1(x: BigInt): BigInt = {
    decreases(max(0,x), 1) // FIXME(measure): Should be inferred by ChainProcessor (cleared)
    f2(x - 2)
  }

  def f2(x: BigInt): BigInt = {
    decreases(max(0,x+2), 0) // FIXME(measure): Should be inferred by ChainProcessor (cleared)
    if (x < 0) 0 else f1(x + 1)
  }
}
