import stainless.lang._
import stainless.collection._

object i497 {
  def pointsToNext(m: BigInt => BigInt, l: List[BigInt], i: BigInt) = {
    0 <= i &&
    i < l.length &&
    m(l(i)) == l((i + 1) % l.length)
  }

  def badLemma(m: BigInt => BigInt, l: List[BigInt], b: BigInt): Boolean = {
    require(pointsToNext(m, l, l.length-1))

    pointsToNext(x => b, l, l.length-1)
  }.holds

  def theorem() = {
    val m1: BigInt => BigInt = x => 1
    val m2: BigInt => BigInt = x => 2
    val l = List[BigInt](1)
    assert(pointsToNext(m1, l, 0))
    assert(!pointsToNext(m2, l, 0))
    badLemma(m1, l, 2)
    assert(pointsToNext(m2, l, 0))
    assert(false)
  }
}