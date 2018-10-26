
import stainless.lang._
import stainless.proof._
import stainless.annotation._

object BigIntMonoidLaws {

  abstract class Monoid[A] {
    def empty: A
    def append(x: A, y: A): A

    @law
    def law_leftIdentity(x: A) = {
      append(empty, x) == x
    }

    @law
    def law_rightIdentity(x: A) = {
      append(x, empty) == x
    }

    @law
    def law_associativity(x: A, y: A, z: A) = {
      append(x, append(y, z)) == append(append(x, y), z)
    }
  }

  def bigIntAdditiveMonoid: Monoid[BigInt] = new Monoid[BigInt] {
    def empty = 0
    def append(x: BigInt, y: BigInt) = x + y
  }

}
