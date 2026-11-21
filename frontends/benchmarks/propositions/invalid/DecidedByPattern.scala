import stainless.lang._

// Matching a proposition against a literal would decide it.
object DecidedByPattern {
  case class Claim(holds: Boolean, at: BigInt)

  def positive(f: BigInt => BigInt): Claim = Claim(forall((x: BigInt) => f(x) > 0), 0)

  def decide(f: BigInt => BigInt): BigInt = positive(f) match {
    case Claim(true, _) => 1
    case _ => 0
  }
}
