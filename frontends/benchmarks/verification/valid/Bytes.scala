/* Copyright 2009-2017 EPFL, Lausanne */

import stainless.lang._

object Bytes {
  def fun() = {
    val b: Byte = 127
    test(b) == 0
  }.holds

  def test(b: Byte) = {
    require(b % 2 != 0)
    if (b > 0) 0 else 1
  }

  def bar(x: Int) = {
    require(x < 128)
    x
  }

  def gun(b: Byte): Int = {
    assert(b >= -128 && b <= 127) // this is not a require!
    bar(b)
  }

  def hun(i: Int) = bar(i.toByte)

  def iun(b: Byte, c: Byte) = {
    b + c
  } ensuring { res => -256 <= res && res <= 254 }

}

