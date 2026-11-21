import stainless.lang._

// A proposition held by data still can't be decided.
object DecidedByField {
  case class Claim(holds: Boolean, at: BigInt)

  def positive(f: BigInt => BigInt): Claim = Claim(forall((x: BigInt) => f(x) > 0), 0)

  def decide(f: BigInt => BigInt): BigInt = if (positive(f).holds) 1 else 0
}
