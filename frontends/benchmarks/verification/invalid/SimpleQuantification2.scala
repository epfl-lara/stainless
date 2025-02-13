/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object SimpleQuantification2 {

  def failling(f: BigInt => BigInt) = {
    require(forall((a: BigInt) => a > 0 ==> f(a) > 1))
    f(1) + f(2)
  }.ensuring { res => res > 4 }
}
