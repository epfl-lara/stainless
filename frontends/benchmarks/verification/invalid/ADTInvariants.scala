/* Coypright 2009-2018 EPFL, Lausanne */

import stainless.lang._

object ADTInvariants {
  case class Positive(var x: BigInt) {
    require(x >= 0)
  }

  def decrease(f: BigInt => Positive, i: BigInt) = {
    val p = f(i)
    p.x = -1
  }
}
