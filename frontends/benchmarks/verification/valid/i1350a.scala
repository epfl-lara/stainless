import stainless.collection._
import stainless.lang._
import stainless.annotation._

object i1350a {
  def test(l: List[BigInt], c: BigInt) = {
    require(l.nonEmpty)
    require(l.forall(i => i == l.head || l.head == i))
    assert(l.forall(i => i == l.head || l.head == i))
  }
}
