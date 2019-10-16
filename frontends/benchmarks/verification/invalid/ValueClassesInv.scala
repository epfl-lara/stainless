import stainless.lang._
import stainless.collection._
import stainless.annotation._

object ValueClassesInv {

  case class Compound[A](xsn: (List[A], BigInt)) extends AnyVal {
    def xs = xsn._1
    def n  = xsn._2

    @invariant
    def inv = xsn._1.length == xsn._2
  }

  def testCompound(d: Compound[BigInt]) = {
    require(d.n == 3)

    d.xs match {
      case Cons(a, Cons(b, Cons(c, Nil()))) =>
        d.copy(xsn = (Nil[BigInt](), a + b + c)) // INVALID
    }
  }
}

