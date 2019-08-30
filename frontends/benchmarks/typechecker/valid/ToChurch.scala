/* From Sereni, PhD thesis 2006 */

import stainless.lang._

object ToChurch {

  def compose[T,U,V](f: U => V, g: T => U): T => V = {
    (x: T) => f(g(x))
  }

  def id[T](x: T) = x

  def succ(x: BigInt) = x + 1

  def toChurch(n: BigInt, f: BigInt => BigInt): BigInt => BigInt = {
    require(n >= 0)
    decreases(n)
    if (n == 0) id[BigInt] _
    else compose(f, toChurch(n - 1, f))
  }

  def main(x: BigInt): BigInt = {
    if (x >= 0) toChurch(x, succ)(0)
    else 0
  }
}

