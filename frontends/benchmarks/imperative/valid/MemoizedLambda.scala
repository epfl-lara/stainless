import stainless.collection._
import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._

@mutable case class Cache(var value: Option[(BigInt, BigInt)]){
  require(value match {
    case Some((x, absX)) => absX == abs(x)
    case _ => true
  })
}

@pure def abs(x: BigInt): BigInt = if (x < 0) -x else x
def memAbs(x: BigInt)(using cache: Cache): BigInt = {
  cache.value match {
    case Some((cachedX, cachedAbs)) if cachedX == x => cachedAbs
    case _ =>
      val result = abs(x)
      cache.value = Some((x, result))
      result
  }
}.ensuring(res => res == abs(x))

def listAbs(xs: List[BigInt]): List[BigInt] = {
  xs.map(abs)
}

case class PureMemAbs(@internallyMutable private val cache: Cache) {
  def apply(x: BigInt): BigInt = {
    cache.value match {
      case Some((cachedX, cachedAbs)) if cachedX == x => cachedAbs
      case _ =>
        val result = abs(x)
        cache.value = Some((x, result))
        result
    }
  }.ensuring(sameAs(abs(x)))
}

def memListAbs(xs: List[BigInt])(using memFunction: PureMemAbs): List[BigInt] = {
  xs.map(memFunction(_))
}.ensuring(res => res == listAbs(xs))
