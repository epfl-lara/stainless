/* Copyright 2009-2017 EPFL, Lausanne */

import stainless.lang._

/**
 * Check that &, | and ^ works on Boolean like it does on Int, with no shortcutting
 */
object BooleanOps {

  def foo1(b: Boolean, d: Boolean): Boolean = {
    var x = 0
    val r = { x += 1; b } & { x *= 2; d }
    assert(x == 2) // always

    r
  } ensuring { res =>
    (res == (b && d)) &&
    (res == toBool(toInt(b) & toInt(d)))
  }

  def foo2(b: Boolean, d: Boolean): Boolean = {
    var x = 0
    val r = { x += 1; b } | { x *= 2; d }
    assert(x == 2) // always

    r
  } ensuring { res =>
    (res == (b || d)) &&
    (res == toBool(toInt(b) | toInt(d)))
  }

  def foo3(b: Boolean, d: Boolean): Boolean = {
    var x = 0
    val r = { x += 1; b } ^ { x *= 2; d }
    assert(x == 2) // always

    r
  } ensuring { res =>
    (res == (b != d)) &&
    (res == toBool(toInt(b) ^ toInt(d)))
  }

  private def toInt(b: Boolean): Int = if (b) 1 else 0
  private def toBool(x: Int): Boolean = {
    require(x == 0 || x == 1)
    x == 1
  }

}

