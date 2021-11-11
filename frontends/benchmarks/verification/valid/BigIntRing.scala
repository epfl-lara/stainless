import stainless.lang._
import stainless.proof._
import stainless.collection._
import stainless.annotation._

object BigIntRing {

  abstract class Additive[A] {
    def zero: A
    def plus(a: A, b: A): A
    def negate(a: A): A

    @law def law_add_associative(x: A, y: A, z: A) = plus(plus(x, y), z) == plus(x, plus(y, z))
    @law def law_add_commutative(x: A, y: A) = plus(x, y) == plus(y, x)
    @law def law_add_identity(x: A) = plus(x, zero) == x
    @law def law_add_inverse(x: A) = plus(x, negate(x)) == zero
  }

  abstract class Ring[A] extends Additive[A] {
    def times(a: A, b: A): A
    def fromInteger(n: BigInt): A
    def one: A = fromInteger(1)

    @law def law_times_associative(x: A, y: A, z: A) = times(times(x, y), z) == times(x, times(y, z))
    @law def law_times_identity(x: A) = times(x, one) == x
    @law def law_left_distributivity(x: A, y: A, z: A) = times(x, plus(y, z)) == plus(times(x, y), times(x, z))
    @law def law_right_distributivity(x: A, y: A, z: A) = times(plus(y, z), x) == plus(times(y, x), times(z, x))
  }

  implicit case object BigIntRing extends Ring[BigInt] {
    override def zero: BigInt = 0
    override def plus(a: BigInt, b: BigInt): BigInt = a + b
    override def negate(a: BigInt): BigInt = -a

    override def times(a: BigInt, b: BigInt): BigInt = a * b
    override def fromInteger(n: BigInt): BigInt = n
    override def one: BigInt = 1
  }

}
