/* From ESOP 2014, Kuwahara et al */

import stainless.lang._

object NestedLoop {

  def loop1(n: BigInt): BigInt = {
    if (n > 0) loop1(n - 1) else 0
  }

  def loop2(n: BigInt): BigInt = {
    if (n > 0) loop1(n) + loop2(n - 1) else 0
  }

}
