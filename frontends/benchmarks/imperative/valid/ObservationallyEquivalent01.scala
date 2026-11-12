import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

object ObservationallyEquivalent01 {
  case class Box(var v: BigInt)
  def pureFactorial(x: BigInt): BigInt = {
    require(x >= 0)
    if (x == 0) then 1
    else x * pureFactorial(x - 1)
  }

  def impureFactorial(b: Box): BigInt = {
    require(b.v >= 0)
    b.v = pureFactorial(b.v)
    b.v
  }.ensuring(res => res == pureFactorial(old(b).v) && b.v == pureFactorial(old(b).v))

  case class Computer(@internallyMutable private var lastComputed: (BigInt, BigInt)){
    require(lastComputed._1 >= 0 && lastComputed._2 == pureFactorial(lastComputed._1))
    def cachedPureFactorial(x: BigInt): BigInt = {
      require(x >= 0)
      if (x == lastComputed._1) then lastComputed._2
      else {
        val result = pureFactorial(x)
        lastComputed = (x, result)
        result
      }
    }.ensuring(sameAs(pureFactorial(x)))

    def cachedImpureFactorial(b: Box): BigInt = {
      require(b.v >= 0)
      if (b.v == lastComputed._1) then b.v = lastComputed._2
      else {
        val result = pureFactorial(b.v)
        lastComputed = (b.v, result)
        b.v = result
      }
      b.v
    }.ensuring(sameAs(impureFactorial(b)))
  }
}
