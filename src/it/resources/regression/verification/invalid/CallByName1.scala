/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object CallByName1 {
  def byName1(i: Int, a: => Int): Int = {
    if (i > 0) a + 1
    else 0
  }

  def byName2(i: Int, a: => Int): Int = {
    if (i > 0) byName1(i - 1, a) + 2
    else 0
  }

  def test(): Boolean = {
    byName1(1, byName2(3, 0)) == 0 && byName1(1, byName2(3, 0)) == 1
  }.holds
}
