
import stainless.lang._
import stainless.proof._
import stainless.annotation._

object BigIntMonoidLaws {

  abstract class Monoid {
    def empty: BigInt
    def append(x: BigInt, y: BigInt): BigInt

    @law
    def law_leftIdentity(x: BigInt) = {
      append(empty, x) == x
    }

    @law
    def law_rightIdentity(x: BigInt) = {
      append(x, empty) == x
    }

    @law
    def law_associativity(x: BigInt, y: BigInt, z: BigInt) = {
      append(x, append(y, z)) == append(append(x, y), z)
    }
  }

  case class AdditiveMonoid() extends Monoid {
    def empty = 0
    def append(x: BigInt, y: BigInt) = x + y
  }

  case class ProductMonoid() extends Monoid {
    def empty = 1
    def append(x: BigInt, y: BigInt) = x * y
  }

}
