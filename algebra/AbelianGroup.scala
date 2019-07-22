package stainless.algebra

import stainless.annotation._

object AbelianGroup {
  import Group._

  abstract class AbelianGroup[A] extends Group[A] {
    @law
    def law_commutative(x: A, y: A): Boolean = {
      combine(x, y) == combine(y, x)
    }
  }

  def additionAbelianGroup: AbelianGroup[BigInt] = new AbelianGroup[BigInt] {
    def combine(x: BigInt, y: BigInt): BigInt = x + y

    def identity: BigInt = 0

    def inverse(x: BigInt): BigInt = -x
  }
}