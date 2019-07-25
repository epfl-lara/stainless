package stainless.algebra

import stainless.annotation._
import stainless.lang.Real

abstract class AbelianGroup[A] extends Group[A] {
  @law
  def law_commutative(x: A, y: A): Boolean = {
    combine(x, y) == combine(y, x)
  }
}

object AbelianGroup {
  // Abelian group for addition of integers
  def additionAbelianGroup: AbelianGroup[BigInt] = new AbelianGroup[BigInt] {
    def combine(x: BigInt, y: BigInt): BigInt = x + y

    def identity: BigInt = 0

    def inverse(x: BigInt): BigInt = -x
  }
}