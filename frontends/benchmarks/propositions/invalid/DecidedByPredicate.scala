import stainless.lang._

// A function that is given a predicate that states a quantifier can't branch on it.
object DecidedByPredicate {
  def count(p: BigInt => Boolean): BigInt = if (p(0)) BigInt(1) else BigInt(0)

  def test(f: BigInt => BigInt): BigInt = count((y: BigInt) => forall((x: BigInt) => f(x) < y))
}
