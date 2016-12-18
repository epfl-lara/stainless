/* Copyright 2009-2016 EPFL, Lausanne */

object Sequencing2 {

  def test(): Int = {
    var x = 0
    x += 5
    x *= 10
    x
  } ensuring(x => x == 50)

}
