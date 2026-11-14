import stainless.lang._

// A proposition is not data: it can't be passed as an argument.
object PassedProposition {
  def negate(b: Boolean): Boolean = !b
  def test(f: BigInt => BigInt): Boolean = negate(forall((x: BigInt) => f(x) > 0))
}
