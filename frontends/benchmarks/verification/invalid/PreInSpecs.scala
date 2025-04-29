/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object PreInSpecs {

  def f(i: BigInt): Boolean = {
    require(i >= 0)
    i > 0
  }

  def g(i: BigInt): Boolean = {
    require(i >= 0)
    i >= -1
  }.holds

  def invoke(i: BigInt): BigInt = {
    require(i == 0 || i > 0 && f(i - 1))
    i + 1
  }.ensuring(res => g(i - 1))

  def invoke2(i: BigInt): BigInt = {
    require(g(i))
    0
  }

}
