/* From ESOP 2014, Kuwahara et al */

import stainless.lang._
import stainless.util._

object AnyDown {

  import Random._

  def max(x: BigInt, y: BigInt) = if (x > y) x else y

  def f(n: BigInt)(implicit state: State): BigInt = {
    decreases(max(n, 0))
    val i = Random.nextBigInt
    val x = if (i < 0) -i else i
    val delta = if (x > 0) x else 1 - x
    val next = n - delta
    if (next > 0) {
      f(next)
    } else {
      BigInt(0)
    }
  }
}
