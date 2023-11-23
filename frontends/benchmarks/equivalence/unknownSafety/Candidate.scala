import stainless.lang._
import stainless.collection._

object Candidate {

  def zero(x: BigInt): BigInt = {
    require(x >= 0)
    if (x > 0) zero(x - 1)
    else x
  }

  def add(x: BigInt, y: BigInt): BigInt = {
    if (x >= 0) {
      val z = zero(x)
      assert(z == 0) // timeout
    }
    x + y
  }

  /////////////////////////////////////

  def isEvenTopLvl(x: BigInt): Boolean = isEven(x)

  def isEven(x: BigInt): Boolean = {
    decreases(if (x <= 0) BigInt(0) else x)
    if (x >= 0) {
      assert(zero(x) == 0) // timeout
    }
    if (x < 0) false
    else if (x == 0) true
    else !isOdd(x - 1)
  }

  def isOdd(x: BigInt): Boolean = {
    decreases(if (x <= 0) BigInt(0) else x)
    if (x <= 0) false
    else if (x == 1) true
    else !isEven(x - 1)
  }

  /////////////////////////////////////

  def isSorted(xs: List[BigInt]): Boolean = xs match {
    case Nil() => true
    case Cons(h, Nil()) =>
      if (h >= 0) {
        assert(zero(h) == 0) // timeout
      }
      true
    case Cons(h1, Cons(h2, t)) => h1 <= h2 && isSorted(t)
  }
}