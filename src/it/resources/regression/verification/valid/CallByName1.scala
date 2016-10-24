/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object CallByName1 {
  def add(a: => Int, b: => Int): Int = a + b

  def test(): Int = {
    add(1,2)
  } ensuring (_ == 3)
}
