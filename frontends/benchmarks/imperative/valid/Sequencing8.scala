/* Copyright 2009-2021 EPFL, Lausanne */

object Sequencing8 {

  def test(): Int = {
    var x = 5

    (x = x + 1, (x = x * 2, (x = x - 1, x = x * 2)))

    x
  } ensuring(res => res == 22)

}
