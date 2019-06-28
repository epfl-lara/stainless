/* Copyright 2009-2018 EPFL, Lausanne */

import stainless.lang._

object Overrides {
  sealed abstract class B {
    def x(a: BigInt): BigInt = {
      require(a > 0)
      BigInt(42)
    } ensuring { _ >= 0 }
  }

  case class C(c: BigInt) extends B {
    require(c >= 0)

    override def x(i: BigInt): BigInt = {
      require(i >= 0)
      decreases(i)
      if (i == 0) BigInt(0)
      else c + x(i-1)
    } ensuring ( _ == c * i )
  }

  case class D() extends B
}
