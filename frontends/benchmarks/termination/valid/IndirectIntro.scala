/* From ESOP 2014, Kuwahara et al */

import stainless.lang._
import stainless.util._

object IndirectIntro {
  case class RandomSequence(f: BigInt => BigInt) {
    def apply(index: BigInt): BigInt = f(index)
  }

  def app(i: BigInt, h: BigInt ~> Unit, v: BigInt): Unit = {
    require(h.pre(v))
    if (i > 0) app(i - 1, h, v) else h(v)
  }

  def abs(i: BigInt): BigInt = if (i < 0) -i else i

  def f(x: BigInt)(implicit random: RandomSequence): Unit =
    if (x > 0) {
      app(
        abs(random(x)),
        PartialFunction { (x2: BigInt) => require(0 <= x2 && x2 < x); f(x2) },
        x - 1)
    } else {
      ()
    }
}
