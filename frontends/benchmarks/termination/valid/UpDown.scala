/* From ESOP 2014, Kuwahara et al */

import stainless.lang._
import stainless.util._
import stainless.util.Random._

object UpDown {

  def app(f: BigInt ~> Unit)(x: BigInt) = {
    require(f.pre(x))
    f(x)
  }

  def down(x: BigInt): Unit = {
    require(x >= 0)
    if (x == 0) {
      ()
    } else {
      down(x - 1)
    }
  }

  def up(x: BigInt): Unit = {
    require(x <= 0)
    if (x == 0) {
      ()
    } else {
      up(x + 1)
    }
  }

  def main(implicit state: State): Unit = {
    val t1 = Random.nextBigInt
    val t2 = Random.nextBigInt
    // with proper extraction, we could directly say that down has type BigInt ~> Unit
    // alternatively, we could write: PartialFunction(down) and treat that specially
    // or also: PartialFunction((x: BigInt) => { require(x >= 0); down(x) })
    val downLambda = ~>(
      (x: BigInt) => x >= 0,
      (x: BigInt) => { unsafe_assume(x >= 0); down(x) }
    )
    val upLambda = ~>(
      (x: BigInt) => x <= 0,
      (x: BigInt) => { unsafe_assume(x <= 0); up(x) }
    )
    if (t1 > 0) app(downLambda)(t1)
    else if (t2 < 0) app(upLambda)(t2)
    else ()
  }
}
