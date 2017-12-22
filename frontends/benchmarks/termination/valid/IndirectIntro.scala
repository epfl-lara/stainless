/* From ESOP 2014, Kuwahara et al */

import stainless.lang._
import stainless.util._
import stainless.util.Random._
import stainless.annotation._

object IndirectIntro {
  def app(i: BigInt, h: BigInt ~> Unit, v: BigInt): Unit = {
    require(h.pre(v))
    if (i > 0) app(i - 1, h, v) else h(v)
  }

  def abs(i: BigInt): BigInt = if (i < 0) -i else i

  def f(x: BigInt)(implicit state: State): Unit =
    if (x > 0) {
      app(
        abs(Random.nextBigInt),
        // with proper extraction, this should be:
        PartialFunction{ (x2: BigInt) => require(0 <= x2 && x2 < x); f(x2) },
        // or
        // ~>((x2: BigInt) => require(0 <= x2 && x2 < x); f(x2))
        /*
         * ~>(
         *   (x2: BigInt) => 0 <= x2 && x2 < x,
         *   (x2: BigInt) => { unsafe_assume(0 <= x2 && x2 < x); f(x2) }
         * ),
         */
        x - 1)
    } else {
      ()
    }
}
