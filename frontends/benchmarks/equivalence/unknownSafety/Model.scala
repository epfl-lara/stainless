import stainless.lang._
import stainless.collection._

object Model {

  def add(x: BigInt, y: BigInt): BigInt = x + y

  /////////////////////////////////////

  def isEvenTopLvl(x: BigInt): Boolean = isEven(x)

  def isEven(x: BigInt): Boolean = {
    decreases(if (x <= 0) BigInt(0) else x)
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
    case Cons(_, Nil()) => true
    case Cons(h1, Cons(h2, t)) => h1 <= h2 && isSorted(t)
  }
}