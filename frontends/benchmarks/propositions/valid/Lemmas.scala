import stainless.lang._

// Quantifiers that only state specifications: predicate definitions, lemmas that hold,
// named propositions, preconditions and assertions.
object Lemmas {
  def isAssociative(f: (BigInt, BigInt) => BigInt): Boolean =
    forall((x: BigInt, y: BigInt, z: BigInt) => f(f(x, y), z) == f(x, f(y, z)))

  def isCommutative(f: (BigInt, BigInt) => BigInt): Boolean =
    forall((x: BigInt, y: BigInt) => f(x, y) == f(y, x))

  // a predicate defined from other predicates
  def isMonoidal(f: (BigInt, BigInt) => BigInt): Boolean =
    isAssociative(f) && isCommutative(f)

  // the result of the postcondition is a proposition
  def additionIsMonoidal: Boolean = {
    isMonoidal((x: BigInt, y: BigInt) => x + y)
  }.holds

  // a proposition can be named, and decides between propositions
  def swapped(f: (BigInt, BigInt) => BigInt, a: BigInt, b: BigInt): Boolean = {
    require(isCommutative(f))
    val commutes = isCommutative(f)
    assert(commutes)
    if (commutes) f(a, b) == f(b, a) else isAssociative(f)
  }.holds

  // a term that doesn't depend on the propositions that are stated around it
  def apply(f: (BigInt, BigInt) => BigInt, a: BigInt, b: BigInt): BigInt = {
    require(isCommutative(f))
    f(a, b)
  }.ensuring(res => res == f(b, a) && isCommutative(f))
}
