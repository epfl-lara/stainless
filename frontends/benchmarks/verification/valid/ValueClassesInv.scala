import stainless.lang._
import stainless.collection._
import stainless.annotation._

object ValueClassesInv {

  case class TestVal(x: Int) extends AnyVal {
    @invariant
    def inv = {
      x > 0 && x != 42
    }
  }

  def testVal1(y: TestVal) = {
    y.x
  } ensuring { _ != 42 }

  def testVal2(y: Int) = {
    require(y >= 0 && y < 100)
    TestVal(y + 93).x
  } ensuring { _ != 42 }

  case class Compound[A](xsn: (List[A], BigInt)) extends AnyVal {
    def xs = xsn._1
    def n  = xsn._2

    @invariant
    def inv = xsn._1.length == xsn._2
  }

  def testCompound(d: Compound[BigInt]) = {
    require(d.n == 3)

    d.xs match {
      case Cons(a, Cons(b, Cons(c, Nil()))) => a + b + c
    }
  }
}

