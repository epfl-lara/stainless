/* From ESOP 2014, Kuwahara et al */

import stainless.lang._

object NestedLoop {

  def max(x: BigInt, y: BigInt) = if (x > y) x else y

  def loop1(n: BigInt): BigInt = {
    decreases(max(n, 0), 0)
    if (n > 0) loop1(n - 1) else 0
  }

  def loop2(n: BigInt): BigInt = {
    decreases(max(n, 0), 1)
    if (n > 0) loop1(n) + loop2(n - 1) else 0
  }

}
