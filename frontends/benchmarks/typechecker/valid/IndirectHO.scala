/* From ESOP 2014, Kuwahara et al */

import stainless.lang._

object IndirectHO {

  def max(x: BigInt, y: BigInt) = if (x > y) x else y

  def app(h: () => () => Unit): () => Unit = h()

  def f(n: BigInt): () => Unit = {
    decreases(max(0, n))
    if (n > 0) {
      app(() => f(n - 1))
    } else {
      () => ()
    }
  }
}
