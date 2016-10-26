/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object CharCompare {
  def cmp(c1: Char, c2: Char): Boolean = { c1 < c2 }.holds
}
