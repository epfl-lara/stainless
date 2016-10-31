/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object SimpleQuantification {

  def failling(f: BigInt => BigInt) = {
    require(forall((a: BigInt) => a > 0 ==> f(a) > 0))
    f(-1)
  } ensuring { res => res > 0 }
}
