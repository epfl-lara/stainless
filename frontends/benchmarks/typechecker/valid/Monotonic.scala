/* Copyright 2009-2018 EPFL, Lausanne */

import stainless.lang._

object Monotonic {
  // TYPEFIX: forall
  // def composeMonotonic(f: BigInt => BigInt, g: BigInt => BigInt): BigInt => BigInt = {
  //   require(forall((a: BigInt, b: BigInt) => (a > b ==> f(a) > f(b)) && (a > b ==> g(a) > g(b))))
  //   (x: BigInt) => f(g(x))
  // } ensuring { res => forall((a: BigInt, b: BigInt) => a > b ==> res(a) > res(b)) }
}

// vim: set ts=4 sw=4 et:
