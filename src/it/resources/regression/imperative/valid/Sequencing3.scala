/* Copyright 2009-2016 EPFL, Lausanne */

object Sequencing3 {

  def f(x: Int): Int = {
    require(x < 10)
    x
  }

  def test(): Int = {
    var x = 0
    f(x)
    x += 5
    f(x)
    x += 5

    x
  }

}
