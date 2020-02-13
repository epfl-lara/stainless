import stainless.lang._
import stainless.annotation._

object ValueClasses {

  type TwoPos = (Positive, Positive)

  def addTwo(two: TwoPos): Positive = {
    Positive(two._1.toBigInt + two._2.toBigInt)
  }

  case class Positive(toBigInt: BigInt) extends AnyVal {
    def isPositive = toBigInt >= 0
  }

  def addPos(x: Positive, y: Positive): Positive = {
    Positive(x.toBigInt + y.toBigInt)
  }

  case class SomeClass[A](pos: Positive, a: A, set: Ops[(A, Positive)]) {
    def doSomething(b: A) = {
      Set((a, pos)).filter { case (c, p) =>
        a == b && a == c && p.isPositive
      }
    }
  }

  def test = {
    val res = addPos(Positive(1), Positive(2))
    assert(res.toBigInt == 3)
    assert(res.isPositive)
  }

  implicit class Ops[A](val set: Set[A]) extends AnyVal {
    @extern @pure
    def filter(p: A => Boolean): Set[A] = {
      new Set(set.theSet.filter(p))
    } ensuring { res =>
      forall((a: A) => (set.contains(a) && p(a)) == res.contains(a))
    }
  }

  val oneToSix = Set[BigInt](1,2,3,4,5,6)

  def test_setFilter(set: Set[BigInt]) = {
    require((set & oneToSix) == oneToSix)

    val res = set.filter(_ < 4)

    assert(res.contains(1))
    assert(res.contains(2))
    assert(res.contains(3))
    assert(!res.contains(4))
    assert(!res.contains(5))
    assert(!res.contains(6))
  }
}

