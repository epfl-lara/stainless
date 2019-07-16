package stainless.algebra

import stainless.annotation._

object BoundedMeetSemilattice {
  import MeetSemilattice._

  abstract class BoundedMeetSemilattice[A] extends MeetSemilattice[A] {
    def one: A

    @law
    def law_identity(x: A): Boolean = {
      meet(x, one) == x
    }
  }
}
