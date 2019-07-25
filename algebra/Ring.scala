package stainless.algebra

import stainless.annotation._

abstract class Ring[A] {
  def addition: AbelianGroup[A]

  def multiplication: Monoid[A]

  final def zero: A = addition.identity

  final def one: A = multiplication.identity

  @law
  def law_leftDistributivity(x: A, y: A, z: A): Boolean = {
    multiplication.combine(x, addition.combine(y, z)) == addition.combine(multiplication.combine(x, y), multiplication.combine(x, z))
  }

  @law
  def law_rightDistributivity(x: A, y: A, z: A): Boolean = {
    multiplication.combine(addition.combine(y, z), x) == addition.combine(multiplication.combine(y, x), multiplication.combine(z, x))
  }
}

object Ring {
  import AbelianGroup._
  import Monoid._

  def ringBigInt: Ring[BigInt] = new Ring[BigInt] {
    def addition: AbelianGroup[BigInt] = additionAbelianGroup

    def multiplication: Monoid[BigInt] = new Monoid[BigInt] {
      def identity: BigInt = 1
      def combine(x: BigInt, y: BigInt): BigInt = x * y
    }
  }
}