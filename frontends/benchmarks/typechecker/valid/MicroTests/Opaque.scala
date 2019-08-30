import stainless.annotation._
import stainless.collection._
import stainless.lang._

object Opaque {

  @opaque
  def size[A](list: List[A]): BigInt = {
    decreases(list)
    list match {
      case Cons(x, xs) => 1 + size(xs)
      case _ => BigInt(0)
    }
  } ensuring (_ >= BigInt(0))

}
