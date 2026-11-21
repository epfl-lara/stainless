import stainless.lang._

// The equality of data that holds propositions is a proposition, so it can't be decided.
object DecidedByEquality {
  case class Claim(holds: Boolean, at: BigInt)

  def positive(f: BigInt => BigInt): Claim = Claim(forall((x: BigInt) => f(x) > 0), 0)

  def decide(f: BigInt => BigInt, g: BigInt => BigInt): BigInt =
    if (positive(f) == positive(g)) 1 else 0
}
