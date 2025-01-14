/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object SimpleQuantification3 {

  def failling(f: BigInt => BigInt, g: BigInt => BigInt, x: BigInt) = {
    require(forall((a: BigInt, b: BigInt) => f(a) + g(a) > 0))
    if(x < 0) f(x) + g(x)
    else x // Postcondition does not hold for x == 0
 }.ensuring { res => res > 0 }
}
