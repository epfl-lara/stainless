/* Copyright 2009-2019 EPFL, Lausanne */

import stainless._
import lang._
import annotation._
import math._

/**
 * A collection of functions that use higher-order functions in various ways
 */
object HOTest {
  def hoRecur(x: BigInt, f: BigInt => BigInt): BigInt = {
    require(x >= 0 && forall((x: BigInt) => f(x) < x && f(x) >= 0))
    decreases(abs(x))
    if (x <= 0) BigInt(0)
    else
      hoRecur(f(x), f)
  }
  
  
}
