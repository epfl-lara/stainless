package stainless.algebra

import stainless.annotation._

object MeetSemilattice {
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
}
