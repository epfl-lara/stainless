package stainless.algebra

import stainless.annotation._
import stainless.math.Nat

object TestSemilattice {
  import JoinSemilattice._
  import MeetSemilattice._
  import BoundedJoinSemilattice._
  import BoundedMeetSemilattice._

  case class Max() extends JoinSemilattice[BigInt] {
    def join(x: BigInt, y: BigInt): BigInt = stainless.math.max(x, y)
  }

  case class Min() extends MeetSemilattice[BigInt] {
    def meet(x: BigInt, y: BigInt): BigInt = stainless.math.min(x, y)
  }

  case class MaxBounded() extends BoundedJoinSemilattice[Nat] {
    def zero: Nat = Nat(0)

    def join(x: Nat, y: Nat): Nat = stainless.math.max(x, y)
  }

  case class AndBoolean() extends BoundedMeetSemilattice[Boolean] {
    def one: Boolean = true

    def meet(x: Boolean, y: Boolean): Boolean = x && y
  }
}
