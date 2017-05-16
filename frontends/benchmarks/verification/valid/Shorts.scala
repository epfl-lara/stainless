/* Copyright 2009-2017 EPFL, Lausanne */

import stainless.lang._

object Shorts {
  def fun() = {
    val b: Short = 32767
    test(b) == 0
  }.holds

  def test(b: Short) = {
    require(b % 2 != 0)
    if (b > 0) 0 else 1
  }

  def bar(x: Int) = {
    require(x < 32768)
    x
  }

  def gun(b: Short): Int = {
    assert(b >= -32768 && b <= 32767) // this is not a require!
    bar(b)
  }

  def hun(i: Int) = bar(i.toByte)

  def iun(b: Short, c: Short) = {
    b + c
  } ensuring { res => -65536 <= res && res <= 65534 }

}

