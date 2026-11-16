import stainless.lang._

// A set computes with the equality of its elements, so it can't hold propositions.
object SetOfPropositions {
  def props(f: BigInt => BigInt): Set[Boolean] = Set(forall((x: BigInt) => f(x) > 0))
}
