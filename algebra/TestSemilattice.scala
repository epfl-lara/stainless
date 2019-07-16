package stainless.algebra

import stainless.annotation._
import stainless.math.Nat

object TestSemilattice {
  import JoinSemilattice._
  import MeetSemilattice._
  import BoundedJoinSemilattice._
  import BoundedMeetSemilattice._

  def maxSemilattice: JoinSemilattice[BigInt] = new JoinSemilattice[BigInt] {
    def join(x: BigInt, y: BigInt): BigInt = stainless.math.max(x, y)
  }

  def minSemilattice: MeetSemilattice[BigInt] = new MeetSemilattice[BigInt] {
    def meet(x: BigInt, y: BigInt): BigInt = stainless.math.min(x, y)
  }

  def maxNatSemilattice: BoundedJoinSemilattice[Nat] = new BoundedJoinSemilattice[Nat] {
    def zero: Nat = Nat(0)

    def join(x: Nat, y: Nat): Nat = stainless.math.max(x, y)
  }

  def andSemilattice: BoundedMeetSemilattice[Boolean] = new BoundedMeetSemilattice[Boolean] {
    def one: Boolean = true

    def meet(x: Boolean, y: Boolean): Boolean = x && y
  }
}
