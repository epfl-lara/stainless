/* From ESOP 2014, Kuwahara et al */

import stainless.lang._

object Indirect {

  def app(f: BigInt => (() => BigInt), arg: BigInt): () => BigInt = {
    () => f(arg)()
  }

  def f(x: BigInt): () => BigInt = {
    if (x > 0) {
      app((i: BigInt) => f(i), x - 1)
    } else {
      () => BigInt(0)
    }
  }

  def main(): BigInt = f(0)()
}
