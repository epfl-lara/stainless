/* Copyright 2009-2017 EPFL, Lausanne */

import stainless.lang._

object Longs {
  def fun() = {
    val l = 8589934592L
    val m = 1073741824L
    l / m == 8
  }.holds

  def gun(i: Byte, j: Int): Long = {
    require(0 <= j && j < 32)
    i.toLong << j
  } ensuring { res =>
    pow(2, j) * i == res
  }

  def pow(x: Long, y: Long): Long = {
    require(y >= 0)
    if (y == 0) 1
    else x * pow(x, y - 1)
  }
}

