/* From LMCS 2008, Sereni et al */

import stainless.lang._

object XPlus2N {

  def succ(x: BigInt) = x + 1

  def g(r: BigInt => BigInt)(a: BigInt) = r(r(a))

  def f(n: BigInt): BigInt => BigInt = {
    require(n >= 0)
    decreases(n)
    if (n == 0) succ _
    else (x: BigInt) => g(f(n - 1))(x)
  }

  def main(n: BigInt)(x: BigInt): BigInt = if (n >= 0 && x >= 0) f(n)(x) else 0
}
