import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._
import stainless.collection._

object ObservationallyPureReferencePrecondition {
  @pure
  def pureFactorial(x: BigInt): BigInt = {
    require(x >= 0)
    decreases(x)
    if (x == 0) then 1
    else x * pureFactorial(x - 1)
  }

  class Computer(@internallyMutable private var lastComputed: (BigInt, BigInt)) {
    require(lastComputed._1 >= 0 && lastComputed._2 == pureFactorial(lastComputed._1))

    def cachedFactorial(x: BigInt): BigInt = {
      require(x >= 0)
      if (x == lastComputed._1) then lastComputed._2
      else {
        val result = pureFactorial(x)
        lastComputed = (x, result)
        result
      }
    }.ensuring(sameAs(pureFactorial(x)))
  }

  // Each call is replaced by `assert(x >= 0); pureFactorial(x)`
  def twice(c: Computer, x: BigInt): BigInt = {
    require(x >= 0)
    c.cachedFactorial(x) + c.cachedFactorial(x)
  }.ensuring(res => res == 2 * pureFactorial(x))

  // The precondition is checked inside the lambda
  def allFactorials(c: Computer, xs: List[BigInt]): List[BigInt] = {
    xs.map(x => if (x >= 0) c.cachedFactorial(x) else BigInt(0))
  }.ensuring(res => res.size == xs.size)
}
