package stainless.algebra

import stainless.annotation._
import stainless.math.Nat


object BoundedJoinSemilattice {
  import JoinSemilattice._

  abstract class BoundedJoinSemilattice[A] extends JoinSemilattice[A] {
    def zero: A

    @law
    def law_identity(x: A): Boolean = {
      join(x, zero) == x
    }
  }

  def maxNatSemilattice: BoundedJoinSemilattice[Nat] = new BoundedJoinSemilattice[Nat] {
    def zero: Nat = Nat(0)

    def join(x: Nat, y: Nat): Nat = stainless.math.max(x, y)
  }
}
