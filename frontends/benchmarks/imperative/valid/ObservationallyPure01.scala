import stainless.annotation._

object ObservationallyPure01 {
  
  case class Computer(@internallyMutable private var lastComputed: (BigInt, BigInt)){
    def pureFactorial(x: BigInt): BigInt = {
      require(x >= 0)
      if (x == 0) then 1
      else x * pureFactorial(x - 1)
    }
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