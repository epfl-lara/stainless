import stainless.lang._
import stainless.collection._

object TupleCleanup {
  def test1(x: BigInt, y: BigInt): (BigInt, BigInt) = {
    val (xx, yy) = (x, y)
    val boom = Nil[BigInt]().head
    (xx, yy)
  }

  def test2(xs: List[BigInt]): (List[BigInt], List[BigInt]) = {
    decreases(xs)
    xs match {
      case Nil() => (Nil(), Nil())
      case Cons(i, t) =>
        val (s2, g2) = test2(t)
        val boom = Nil[BigInt]().head
        (s2, g2)
    }
  }
}