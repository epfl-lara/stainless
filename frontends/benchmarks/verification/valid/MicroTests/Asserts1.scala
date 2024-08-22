/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._
import stainless.annotation._
import stainless._

object Asserts1 {

  def foo(a: BigInt): BigInt = {
    require(a > 0)

    val x = {
      val b = a
      assert(b > 0, "Hey now")
      b + bar(1)
    }
    assert(x > 2)
    x

  }.ensuring {
    _ > a
  }

  def bar(a: BigInt): BigInt = {
    require(a > 0)

    val x = {
      val b = a
      assert(b > 0, "Hey now")
      b + 2
    }
    assert(x > 2)
    x

  }.ensuring {
    _ > a
  }
}
