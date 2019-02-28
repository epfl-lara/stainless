import stainless.lang._
import stainless.collection._

object Passes2 {

  def sizeOf[A](list: List[A]): BigInt = (list match {
    case Nil()       => BigInt(0)
    case Cons(x, xs) => BigInt(1) + sizeOf(xs)
  }) ensuring { res =>
    res >= 0 &&
    ((list, res) passes {
      case Nil()          => BigInt(0)
      case Cons(_, Nil()) => BigInt(1)
      case Cons(_, _)     => BigInt(2)
    })
  }

}
