/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object Numeric2 {
  def looping1(x: Int): Int = looping2(x - 1)

  def looping2(x: Int): Int = looping3(x - 1)

  def looping3(x: Int): Int = looping4(x - 1)

  def looping4(x: Int): Int = looping1(x + 3)
}

// vim: set ts=4 sw=4 et:
