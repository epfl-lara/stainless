import stainless.lang._
object Countable {
  // an instance of Countable[T] gives a bijection between T and BigInt
  case class Countable[T](f: T => BigInt, g: BigInt => T) {
    require(
      forall((t: T) => g(f(t)) == t) &&
      forall((h: BigInt) => f(g(h)) == h)
    )
  }

  type Empty = Countable[BigInt => BigInt]

  // there is no element of Countable[BigInt => BigInt]
  // (since there is no bijection between BigInt and BigInt => BigInt)
  def lemma(e: Empty) = {
    val f: (BigInt => BigInt) => BigInt = e.f
    val g: BigInt => (BigInt => BigInt) = e.g
    def d(x: BigInt): BigInt = g(x)(x) + 1
    assert(d(f(d)) == g(f(d))(f(d)) + 1)
    assert(d(f(d)) == d(f(d)) + 1)
    false
  }.holds
}
