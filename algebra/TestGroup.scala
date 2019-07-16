package stainless.algebra

import stainless.annotation._
import stainless.math.Nat

object TestGroup {
  import AbelianGroup._
  import Monoid._
  import Ring._

  def additionAbelianGroup: AbelianGroup[BigInt] = new AbelianGroup[BigInt] {
    def combine(x: BigInt, y: BigInt): BigInt = x + y

    def identity: BigInt = 0

    def inverse(x: BigInt): BigInt = -x
  }

  def multiplicationMonoid: Monoid[BigInt] = new Monoid[BigInt] {
    def combine(x: BigInt, y: BigInt): BigInt = x * y

    def identity: BigInt = 1
  }

  def ringBigInt: Ring[BigInt] = new Ring[BigInt] {
    def addition: AbelianGroup[BigInt] = additionAbelianGroup

    def multiplication: Monoid[BigInt] = multiplicationMonoid
  }
}
