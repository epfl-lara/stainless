import stainless.lang._

// A proposition is not data: a function can't return one as a value.
object ReturnedPredicate {
  def bounded(f: BigInt => BigInt): BigInt => Boolean =
    (r: BigInt) => forall((x: BigInt) => f(x) <= r)
}
