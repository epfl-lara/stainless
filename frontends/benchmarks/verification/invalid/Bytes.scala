/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object Bytes {

  def test(b: Byte) = {
    require(b % 2 != 0)
    if (b > 0) 0 else 1
  }

  def fun(b: Byte) = test(b)

  def gun(b: Byte, c: Byte) = {
    b + c
  }.ensuring { res => -128 <= res && res <= 127 } // Invalid, because b + c is promoted to an Int

}

