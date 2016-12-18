/* Copyright 2009-2016 EPFL, Lausanne */

object Sequencing1 {

  def test(): Int = {
    var x = 0
    x += 1
    x *= 2
    x
  } ensuring(x => x == 2)

}
