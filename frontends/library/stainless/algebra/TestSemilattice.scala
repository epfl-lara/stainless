package stainless.algebra

import stainless.annotation._

object TestSemilatice {
  import JoinSemilattice._
  import MeetSemilattice._

  case class Max() extends JoinSemilattice[BigInt] {
    def join(x: BigInt, y: BigInt): BigInt = stainless.math.max(x, y)
  }

  case class Min() extends MeetSemilattice[BigInt] {
    def meet(x: BigInt, y: BigInt): BigInt = stainless.math.min(x, y)
  }
}
