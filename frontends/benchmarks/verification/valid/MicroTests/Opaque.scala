import stainless.annotation._
import stainless.collection._

object Opaque {

  @opaque
  def size[A](list: List[A]): BigInt = (list match {
    case x :: xs => 1 + size(xs)
    case _ => BigInt(0)
  }) ensuring (_ >= BigInt(0))

}
