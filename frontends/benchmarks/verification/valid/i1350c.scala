import stainless.lang._
import stainless.collection._

object i1350c {

  def prop(l: List[BigInt], c: BigInt): Boolean = l.forall { i =>
    val i2 = 2 * i
    if (i == 42) c == i2 || c > i2
    else if (c >= 1) c == i && i <= 10
    else i == c || c == i2
  }

  def test(l: List[BigInt]) = {
    require(l.nonEmpty)
    require(prop(l, l.head))
    assert(l.forall { i =>
      val i2 = 2 * i
      if (i == 42) l.head == i2 || l.head > i2
      else if (l.head >= 1) l.head == i && i <= 10
      else i == l.head || l.head == i2
    })
  }
}
