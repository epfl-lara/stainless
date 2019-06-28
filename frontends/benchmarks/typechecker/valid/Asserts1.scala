/* Copyright 2009-2018 EPFL, Lausanne */

import stainless.lang._
import stainless.annotation._
import stainless._

object Asserts1 {

  def foo(a: BigInt): BigInt = {
    require(a > 0)

    {
      val b = a
      assert(b > 0, "Hey now")
      b + bar(1)
    } ensuring { _ > 2 }

  } ensuring {
    _ > a
  }

  def bar(a: BigInt): BigInt = {
    require(a > 0)

    {
      val b = a
      assert(b > 0, "Hey now")
      b + 2
    } ensuring { _ > 2 }

  } ensuring {
    _ > a
  }
}
