package stainless.algebra

import stainless.annotation._

@library
abstract class MeetSemilattice[A] {
  def meet(x: A, y: A): A

  final def lteqv(x: A, y: A): Boolean = meet(x, y) == x

  @law
  def law_associativity(x: A, y: A, z: A): Boolean = {
    meet(meet(x, y), z) == meet(x, meet(y, z))
  }

  @law
  def law_commutativity(x: A, y: A): Boolean = {
    meet(x, y) == meet(y, x)
  }

  @law
  def law_idempotency(x: A): Boolean = {
    meet(x, x) == x
  }
}

@library
object MeetSemilattice {
  def minSemilattice: MeetSemilattice[BigInt] = new MeetSemilattice[BigInt] {
    def meet(x: BigInt, y: BigInt): BigInt = stainless.math.min(x, y)
  }
}
