import stainless.lang._

// A proof by cases decides between two terms of type Unit, not between a value and a proof.
object DecidedUnitValue {
  def isPositive(f: BigInt => BigInt): Boolean = forall((x: BigInt) => f(x) > 0)

  def test(f: BigInt => BigInt): BigInt = {
    val r = if (isPositive(f)) { (); BigInt(1) } else BigInt(0)
    r
  }
}
