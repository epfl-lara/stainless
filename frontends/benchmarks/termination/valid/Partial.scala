/* From ESOP 2014, Kuwahara et al */

import stainless.lang._

object Partial {

  def maxNegP(j: BigInt, p: BigInt => Boolean): Boolean = {
    !p(j) && forall((k: BigInt) => !p(k) ==> (k <= j))
  }

  def f(x: BigInt, p: BigInt => Boolean): BigInt = {
    // quantifiers are propositions: the existential is stated here rather than passed around
    // as a predicate
    require(!p(x) || !forall((j: BigInt) => !(j < x && maxNegP(j, p))))
    decreases(if (!p(x)) BigInt(0) else x - choose((j: BigInt) => j < x && maxNegP(j, p)))
    if (p(x)) {
      f(x - 1, p)
    } else {
      x
    }
  }
}
