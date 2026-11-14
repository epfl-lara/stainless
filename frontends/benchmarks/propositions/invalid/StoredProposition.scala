import stainless.lang._

// Data can't hold a proposition: its equality would observe which one it is.
object StoredProposition {
  def pair(f: BigInt => BigInt): (Boolean, BigInt) =
    (forall((x: BigInt) => f(x) > 0), f(0))
}
