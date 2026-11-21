import stainless.lang._

// A predicate that states a quantifier is a value: a function can return one.
object ReturnedPredicate {
  def bounded(f: BigInt => BigInt): BigInt => Boolean =
    (r: BigInt) => forall((x: BigInt) => f(x) <= r)
}
