package stainless.algebra

import stainless.annotation._
import stainless.math.Nat

object TestGroup {
  import Group._

  case class Addition() extends Group[BigInt] {
    def combine(x: BigInt, y: BigInt): BigInt = x + y

    def identity: BigInt = 0

    def inverse(x: BigInt): BigInt = -x
  }
}
