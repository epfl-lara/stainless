import stainless.lang._
import stainless.collection._

object i1350b {

  def prop(l: List[BigInt], c: BigInt): Boolean = l.forall(i => i == c || c == i)

  def test(l: List[BigInt]) = {
    require(l.nonEmpty)
    require(prop(l, l.head))
    assert(l.forall(i => i == l.head || l.head == i))
  }
}
