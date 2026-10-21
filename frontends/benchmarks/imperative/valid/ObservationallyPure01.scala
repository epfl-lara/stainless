import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object ObservationallyPure01 {
  @pure
  def pureFactorial(x: BigInt): BigInt = {
    require(x >= 0)
    if (x == 0) then 1
    else x * pureFactorial(x - 1)
  }

  case class Computer(@internallyMutable private var lastComputed: (BigInt, BigInt)){
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
}
