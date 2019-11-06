package stainless.algebra

import stainless.annotation._
import stainless.lang._

@library
abstract class PartialOrder[A] extends Eq[A] {
    def lteq(x: A, y: A): Boolean

    final def partialOrder(x: A, y: A): Option[BigInt] = {
        (lteq(x, y), lteq(y, x)) match {
            case (true, true) => Some(0)
            case (true, false) => Some(-1)
            case (false, true) => Some(1)
            case (false, false) => None[BigInt]()
        }
    }

    @law
    def law_reflexivity_order(x: A): Boolean = {
        lteq(x, x)
    }

    @law
    def law_antisymmetry(x: A, y: A): Boolean = {
        (lteq(x, y) && lteq(y, x)) ==> eq(x, y)
    }

    @law
    def law_transitivity_order(x: A, y: A, z: A): Boolean = {
        (lteq(x, y) && lteq(y, z)) ==> lteq(x, z)
    }
}