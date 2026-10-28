import stainless.annotation._
import stainless.lang._
import stainless.lang.StaticChecks._
import stainless.collection._

object ObservationallyPureHigherOrder {
  @pure
  def fact(x: BigInt): BigInt = {
    decreases(if (x <= 0) BigInt(0) else x)
    if (x <= 0) BigInt(1) else x * fact(x - 1)
  }

  @pure
  def twoFacts(x: BigInt): BigInt = 2 * fact(x)

  class Memo(@internallyMutable private var last: (BigInt, BigInt)) {
    require(last._2 == fact(last._1))

    def apply(x: BigInt): BigInt = {
      if (x == last._1) last._2
      else {
        val r = fact(x)
        last = (x, r)
        r
      }
    }.ensuring(sameAs(fact(x)))

    // Calls on `this` within an observationally pure method keep their effects on the cache
    def applyTwice(x: BigInt): BigInt = {
      apply(x) + apply(x)
    }.ensuring(sameAs(twoFacts(x)))
  }

  // The memoized function is used twice on the same object, as a pure function
  def twice(m: Memo, x: BigInt): BigInt = {
    m(x) + m(x)
  }.ensuring(res => res == 2 * fact(x))

  // ... and as argument of higher-order functions
  def allFacts(m: Memo, l: List[BigInt]): List[BigInt] = {
    l.map(x => m(x))
  }.ensuring(res => res.size == l.size)

  def factsTwice(m: Memo, l: List[BigInt]): List[BigInt] = {
    l.flatMap(x => List(m(x), m(x)))
  }

  def factsOf(l: List[BigInt]): List[BigInt] = {
    decreases(l)
    l match {
      case Nil() => Nil[BigInt]()
      case Cons(h, t) => Cons(fact(h), factsOf(t))
    }
  }

  // Mapping the memoized function gives the factorials
  def mapIsFact(m: Memo, l: List[BigInt]): Unit = {
    decreases(l)
    l match {
      case Nil() => ()
      case Cons(_, t) => mapIsFact(m, t)
    }
  }.ensuring(_ => l.map(x => m(x)) == factsOf(l))
}
