import stainless.lang._
import stainless.proof._

object Countable {
  // an instance of Countable[T] gives a injection of T into BigInt
  trait Countable[T] {
    def f(t: T): BigInt
    def g(x: BigInt): T

    def gof(t: T) = {
      ( ??? : Unit )
    } ensuring(_ => g(f(t)) == t)
  }

  type Empty = Countable[BigInt => BigInt]

  // there is no element of Countable[BigInt => BigInt]
  // since there is no injection of BigInt => BigInt into BigInt
  def lemma(e: Empty) = {
    val f: (BigInt => BigInt) => BigInt = e.f
    val g: BigInt => (BigInt => BigInt) = e.g
    def d(x: BigInt): BigInt = g(x)(x) + 1
    assert(d(f(d)) == g(f(d))(f(d)) + 1)
    e.gof(d)
    check(d(f(d)) == d(f(d)) + 1)
    false
  }.holds
}

