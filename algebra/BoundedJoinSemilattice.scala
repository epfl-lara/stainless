package stainless.algebra

import stainless.annotation._

object BoundedJoinSemilattice {
  import JoinSemilattice._

  abstract class BoundedJoinSemilattice[A] extends JoinSemilattice[A] {
    def zero: A

    @law
    def law_identity(x: A): Boolean = {
      join(x, zero) == x
    }
  }
}
