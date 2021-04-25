/* From ESOP 2014, Kuwahara et al */

import stainless.lang._
import stainless.util._
import stainless.io.State

object Loop2 {

  import Random._

  def f(m: BigInt, n: BigInt)(implicit state: State): BigInt = {
    val r = Random.nextBigInt
    if (r > 0 && m > 0) f(m - 1, n)
    else if (r <= 0 && n > 0) f(m, n - 1)
    else 0
  }
}
