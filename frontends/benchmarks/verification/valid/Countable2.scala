import stainless.lang._
object Countable2 {
  // an instance of Countable[T] gives a bijection between T and BigInt
  abstract class Countable[T] {
    require(
      forall((t: T) => g(f(t)) == t) &&
      forall((h: BigInt) => f(g(h)) == h)
    )

    def f(x: T): BigInt
    def g(x: BigInt): T
  }

  type Empty = Countable[BigInt => BigInt]

  // there is no element of Countable[BigInt => BigInt]
  // (since there is no bijection between BigInt and BigInt => BigInt)
  def lemma(e: Empty) = {
    val f: (BigInt => BigInt) => BigInt = e.f _
    val g: BigInt => (BigInt => BigInt) = e.g _
    def d(x: BigInt): BigInt = g(x)(x) + 1
    assert(d(f(d)) == g(f(d))(f(d)) + 1)
    assert(d(f(d)) == d(f(d)) + 1)
    false
  }.holds

  /* true but unprovable with current quantifier module
  def theorem() = {
    assert(forall((e: Empty) => lemma(e)))
    forall((e: Empty) => false)
  }.holds
  */
}
