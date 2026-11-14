/* From ESOP 2014, Kuwahara et al */

import stainless.lang._

object Partial {

  def exists[T](p: T => Boolean): Boolean = {
    !forall((t: T) => !p(t))
  }

  def eliminate_exists[T](p: T => Boolean): T = {
    require(exists[T](p))
    choose[T]((res: T) => p(res))
 }.ensuring(p)

  def maxNegP(j: BigInt, p: BigInt => Boolean): Boolean = {
    !p(j) && forall((k: BigInt) => !p(k) ==> (k <= j))
  }

  def f(x: BigInt, p: BigInt => Boolean): BigInt = {
    require(!p(x) || exists[BigInt]((j: BigInt) => j < x && maxNegP(j, p)))
    decreases(if (!p(x)) BigInt(0) else x - eliminate_exists[BigInt]((j: BigInt) => j < x && maxNegP(j, p)))
    if (p(x)) {
      f(x - 1, p)
    } else {
      x
    }
  }
}
