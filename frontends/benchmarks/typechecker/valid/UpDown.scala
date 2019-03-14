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
    decreases(x)
    if (x == 0) {
      ()
    } else {
      down(x - 1)
    }
  }

  def up(x: BigInt): Unit = {
    require(x <= 0)
    decreases(-x)
    if (x == 0) {
      ()
    } else {
      up(x + 1)
    }
  }

  def main(implicit state: State): Unit = {
    val t1 = Random.nextBigInt
    val t2 = Random.nextBigInt
    val downLambda = PartialFunction { (x: BigInt) =>
      require(x >= 0)
      down(x)
    }
    val upLambda = PartialFunction { (x: BigInt) =>
      require(x <= 0)
      up(x)
    }
    if (t1 > 0) app(downLambda)(t1)
    else if (t2 < 0) app(upLambda)(t2)
    else ()
  }
}
