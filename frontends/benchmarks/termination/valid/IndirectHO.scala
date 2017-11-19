/* From ESOP 2014, Kuwahara et al */

import stainless.lang._

object IndirectHO {

  def app(h: () => () => Unit): () => Unit = h()

  def f(n: BigInt): () => Unit = {
    if (n > 0) {
      app(() => f(n - 1))
    } else {
      () => ()
    }
  }
}
