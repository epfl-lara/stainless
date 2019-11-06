package stainless.algebra

import stainless.annotation._
import stainless.lang._
import stainless.proof._
import stainless.math.Nat

@library
abstract class TotalOrder[A] extends PartialOrder[A] {
    final def compare(x: A, y: A): BigInt = {
        assert(law_connex(x, y))

        (lteq(x, y), lteq(y, x)) match {
            case (true, true) => 0
            case (true, false) => -1
            case (false, true) => 1
            case (false, false) => error[BigInt]("Impossible case because of law connex")
        }
    }

    @law
    def law_connex(x: A, y: A): Boolean = {
        lteq(x, y) || lteq(y, x)
    }
}

@library
object TotalOrder {
    def bigIntTotalOrder: TotalOrder[BigInt] = new TotalOrder[BigInt] {
        def eq(x: BigInt, y: BigInt): Boolean = {
            x == y
        }

        def lteq(x: BigInt, y: BigInt): Boolean = {
            x <= y
        }
    }

    def natTotalOrder: TotalOrder[Nat] = new TotalOrder[Nat] {
        def eq(x: Nat, y: Nat) = x == y

        def lteq(x: Nat, y: Nat) = x <= y
    }
}