
import stainless.lang._
import stainless.collection._
import stainless.annotation._

object InductParams {

  abstract class Semigroup[A] {
    def append(x: A, y: A): A

    @law
    def law_associativity(x: A, y: A, z: A): Boolean = {
      append(append(x, y), z) == append(x, append(y, z))
    }
  }

  case class ListSemigroup[A]() extends Semigroup[List[A]] {
    def append(left: List[A], right: List[A]): List[A] = left ++ right

    @induct("xxs")
    override def law_associativity(xxs: List[A], ys: List[A], zs: List[A]): Boolean = {
      super.law_associativity(xxs, ys, zs)
    }
  }

}
