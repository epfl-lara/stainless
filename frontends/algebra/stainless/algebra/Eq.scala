package stainless.algebra

import stainless.annotation._
import stainless.lang._

@library
abstract class Eq[A] {
    def eq(x: A, y: A): Boolean

    @law
    def law_reflexivity(x: A): Boolean = {
        eq(x, x)
    }

    @law
    def law_symmetry(x: A, y: A): Boolean = {
        eq(x, y) == eq(y, x)
    }

    @law
    def law_transitivity(x: A, y: A, z: A): Boolean = {
        (eq(x, y) && eq(y, z)) ==> eq(x, z)
    }
}