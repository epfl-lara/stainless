package stainless.algebra

import stainless.annotation._

@library
abstract class BoundedMeetSemilattice[A] extends MeetSemilattice[A] {
  def one: A

  @law
  def law_identity(x: A): Boolean = {
    meet(x, one) == x
  }
}

@library
object BoundedMeetSemilattice {
  def andSemilattice: BoundedMeetSemilattice[Boolean] = new BoundedMeetSemilattice[Boolean] {
    def one: Boolean = true

    def meet(x: Boolean, y: Boolean): Boolean = x && y
  }
}
