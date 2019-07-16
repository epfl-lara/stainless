package stainless.algebra

import stainless.annotation._

object Monoid {
  import Semigroup._

  abstract class Monoid[A] extends Semigroup[A] {
    def identity: A

    @law
    def law_leftIdentity(x: A): Boolean = {
      combine(identity, x) == x
    }

    @law
    def law_rightIdentity(x: A): Boolean = {
      combine(x, identity) == x
    }
  }
}