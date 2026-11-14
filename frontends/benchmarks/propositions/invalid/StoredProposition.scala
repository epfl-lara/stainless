import stainless.lang._

// A proposition is not data: it can't be stored.
object StoredProposition {
  def pair(f: BigInt => BigInt): (Boolean, BigInt) =
    (forall((x: BigInt) => f(x) > 0), f(0))
}
