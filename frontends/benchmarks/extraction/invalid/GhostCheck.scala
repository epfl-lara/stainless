// See https://github.com/epfl-lara/stainless/issues/346

import stainless.lang._
import stainless.annotation._
import stainless.collection._

object Ghost3 {
  case class Ghost3(@ghost var l: List[BigInt]) {
    def f(x: BigInt) = {
      ghost {
        l = x :: l // Argument to ghost parameter `value` of `ghost` must only have effects on ghost fields
      }
    }
  }
}

object Ghost4 {
  case class Ghost4(@ghost var l: List[BigInt]) {
    @ghost
    def add(x: BigInt) = {
      l = x :: l // Ghost function cannot have effect on non-ghost state
    }
  }
}
