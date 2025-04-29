/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object HOInvocations {
  def switch(x: Int, f: (Int) => Int, g: (Int) => Int) = if (x > 0) f else g

  def failling_1(f: (Int) => Int) = {
    switch(-10, (x: Int) => x + 1, f)(2)
  }.ensuring { res => res > 0 }

  def failling_2(x: Int, f: (Int) => Int, g: (Int) => Int) = {
    require(x > 0)
    switch(1, switch(x, f, g), g)(1)
  }.ensuring { res => res != f(1) }
}

// vim: set ts=4 sw=4 et:
