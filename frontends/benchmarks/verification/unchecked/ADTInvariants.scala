/* Coypright 2009-2018 EPFL, Lausanne */

import stainless.lang._

// Note @nv: we can't actually run check-models on adt invariant violations
//           since the adt invariant check is of the shape
//              path ==> inv(adt)
//           and the construction of `adt` will lead to an invariant violation
//           (hence a crash).
object ADTInvariants {
  case class Positive(var x: BigInt) {
    require(x >= 0)
  }

  def decrease(f: BigInt => Positive, i: BigInt) = {
    val p = f(i)
    p.x = -1
  }
}
