package stainless.algebra

import stainless.annotation._

object AbelianGroup {
  import Group._

  abstract class AbelianGroup[A] extends Group[A] {
    @law
    def law_commutative(x: A, y: A): Boolean = {
      combine(x, y) == combine(y, x)
    }
  }
}