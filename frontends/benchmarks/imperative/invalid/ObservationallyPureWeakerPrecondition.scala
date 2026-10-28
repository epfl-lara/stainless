import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object ObservationallyPureWeakerPrecondition {
  @pure
  def pred(x: BigInt): BigInt = {
    require(x > 0)
    x - 1
  }

  class Memo(@internallyMutable private var last: (BigInt, BigInt)) {
    require(last._1 > 0 && last._2 == pred(last._1))

    // Missing `require(x > 0)`: the precondition of `pred` fails in the postcondition
    def get(x: BigInt): BigInt = {
      if (x == last._1) last._2
      else if (x <= 0) BigInt(0)
      else {
        val result = pred(x)
        last = (x, result)
        result
      }
    }.ensuring(sameAs(pred(x)))
  }
}
