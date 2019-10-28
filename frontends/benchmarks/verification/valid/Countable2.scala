import stainless.lang._
import stainless.annotation._

object Countable2 {
  // an instance of Countable[T] gives a bijection between T and BigInt
  abstract class Countable[T] {
    @law
    def isBijective = {
      forall((t: T) => g(f(t)) == t) &&
      forall((h: BigInt) => f(g(h)) == h)
    }

    def f(x: T): BigInt
    def g(x: BigInt): T
  }

  type Empty = Countable[BigInt => BigInt]

  // there is no element of Countable[BigInt => BigInt]
  // (since there is no bijection between BigInt and BigInt => BigInt)
  def lemma(e: Empty) = {
    assert(e.isBijective)
    val f: (BigInt => BigInt) => BigInt = e.f _
    val g: BigInt => (BigInt => BigInt) = e.g _
    def d(x: BigInt): BigInt = g(x)(x) + 1
    assert(d(f(d)) == g(f(d))(f(d)) + 1)
    assert(d(f(d)) == d(f(d)) + 1)
    false
  }.holds

  def theorem() = {
    if (forall((x: Empty) => false))
      assert(false) // Inox assumes every type is not empty
    else {
      val e: Empty = choose((x: Empty) => true)
      assert(lemma(e))
      assert(false)
    }
  }
}
