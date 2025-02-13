/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._
import stainless.annotation._
import stainless._

object Asserts1 {

  def foo(a: Int): Int = {
    require(a > 0)
    val b = a
    assert(b > 0, "Hey now")
    b + bar(1)
  }.ensuring { res =>
    res > a && res < 2
  }

  def bar(a: Int): Int = {
    require(a > 0)
    val b = a
    assert(b > 0, "Hey now")
    b + 2
  }.ensuring { res =>
    res > a && res > 2
  }
}
