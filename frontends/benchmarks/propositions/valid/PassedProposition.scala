import stainless.lang._

// A proposition is a value: it can be passed to a function that only states it, which makes
// the parameter and the result of that function propositions.
object PassedProposition {
  def negate(b: Boolean): Boolean = !b
  def test(f: BigInt => BigInt): Boolean = negate(forall((x: BigInt) => f(x) > 0))
}
