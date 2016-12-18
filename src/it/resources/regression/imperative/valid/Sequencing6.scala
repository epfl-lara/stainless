/* Copyright 2009-2016 EPFL, Lausanne */

object Sequencing6 {

  def f(x1: Int, x2: Int, x3: Int): Int = {
    require(x1 == 6 && x2 == 12 && x3 == 11)
    x3
  }

  def test(): Int = {
    var x = 5

    f(
      {x = x + 1; x},
      {x = x * 2; x},
      {x = x - 1; x}
    )

    x

  } ensuring(res => res == 11)

}
