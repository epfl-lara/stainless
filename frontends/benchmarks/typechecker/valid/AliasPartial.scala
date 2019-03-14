/* From L. Ledesma-Garza and A. Rybalchenko */

import stainless.lang._

object AliasPartial {
  def max(x: BigInt, y: BigInt) = if (x > y) x else y

  def f(x: BigInt)(y: BigInt): BigInt = {
    decreases(max(0, x))
    if (x > 0) f(x - 1)(y)
    else lambda(y)
  }

  def lambda(x: BigInt): BigInt = x + 1

  def g(x: BigInt) = f(1)(x)

  def main = g(2)
}
