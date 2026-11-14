import stainless.lang._

// The refinement of a proposition states what holds of it, here in terms of the arguments
// of the predicate. A refined proposition is still a proposition.
object RefinedPredicates {
  def isPositive(f: BigInt => BigInt): {r: Boolean with !r || f(0) > 0} =
    forall((x: BigInt) => f(x) > 0)

  def arePositive(f: BigInt => BigInt, g: BigInt => BigInt): Boolean =
    isPositive(f) && isPositive(g)

  def named(f: BigInt => BigInt): Boolean = {
    val positive: {p: Boolean with !p || f(0) > 0} = isPositive(f)
    !positive || f(0) > 0
  }.holds
}
