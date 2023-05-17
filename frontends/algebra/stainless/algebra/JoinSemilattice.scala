package stainless.algebra

import stainless.annotation._

@library
abstract class JoinSemilattice[A] {
  def join(x: A, y: A): A

  final def lteqv(x: A, y: A): Boolean = join(x, y) == y

  @law
  def law_associativity(x: A, y: A, z: A): Boolean = {
    join(join(x, y), z) == join(x, join(y, z))
  }

  @law
  def law_commutativity(x: A, y: A): Boolean = {
    join(x, y) == join(y, x)
  }

  @law
  def law_idempotency(x: A): Boolean = {
    join(x, x) == x
  }
}

@library
object JoinSemilattice {
  def maxSemilattice: JoinSemilattice[BigInt] = new JoinSemilattice[BigInt] {
    def join(x: BigInt, y: BigInt): BigInt = stainless.math.max(x, y)
  }
}
