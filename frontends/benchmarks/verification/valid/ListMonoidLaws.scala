
import stainless.lang._
import stainless.collection._
import stainless.annotation._
import stainless.proof._

object ListMonoidLaws {

  abstract class Monoid {

    def empty: List[BigInt]
    def append(left: List[BigInt], right: List[BigInt]): List[BigInt]

    @law
    def law_leftIdentity(x: List[BigInt]): Boolean = {
      append(empty, x) == x
    }

    @law
    def law_rightIdentity(x: List[BigInt]): Boolean = {
      append(x, empty) == x
    }

    @law
    def law_associativity(x: List[BigInt], y: List[BigInt], z: List[BigInt]): Boolean = {
      append(append(x, y), z) == append(x, append(y, z))
    }
  }

  case class ListMonoid() extends Monoid {
    def empty = Nil[BigInt]()
    def append(left: List[BigInt], right: List[BigInt]): List[BigInt] = left ++ right

    override def law_associativity(xxs: List[BigInt], ys: List[BigInt], zs: List[BigInt]): Boolean = {
      super.law_associativity(xxs, ys, zs) because {
        xxs match {
          case Nil() =>
            true
          case Cons(x, xs) =>
            law_associativity(xs, ys, zs)
        }
      }
    }
  }

}
