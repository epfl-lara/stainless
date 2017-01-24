/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object Numeric1 {
  // division by 0 loops
  def looping(x: Int, y: Int): Int = {
    if (x < y) 0
    else 1 + looping(x - y, y)
  }
}

// vim: set ts=4 sw=4 et:
