/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object Numeric3 {
  def looping(x: Int) : Int = if (x > 0) looping(x - 1) else looping(2)
}


// vim: set ts=4 sw=4 et:
