import stainless.lang._

// Data can hold propositions: fields, tuples and map values that are given one are
// propositions, and the equality of such data is a proposition too.
object StoredProposition {
  case class Claim(holds: Boolean, at: BigInt)

  def positive(f: BigInt => BigInt): Claim = Claim(forall((x: BigInt) => f(x) > 0), 0)

  def pair(f: BigInt => BigInt): (Boolean, BigInt) =
    (forall((x: BigInt) => f(x) > 0), f(0))

  def useClaim(f: BigInt => BigInt): Unit = {
    require(positive(f).holds)
    assert(f(3) > 0)
  }

  def usePair(f: BigInt => BigInt): Unit = {
    require(pair(f)._1)
    assert(f(3) > 0)
  } ensuring(_ => pair(f)._2 > 0)

  def sameClaims(f: BigInt => BigInt, g: BigInt => BigInt): Unit = {
    require(positive(f) == positive(g) && positive(f).holds)
    assert(g(3) > 0)
  }

  def plain(f: BigInt => BigInt): Boolean = positive(f).at == 0
}
