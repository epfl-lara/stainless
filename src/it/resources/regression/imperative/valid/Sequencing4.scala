/* Copyright 2009-2016 EPFL, Lausanne */

object Sequencing4 {

  def test(): Int = {
    var x = 5

    {x = x + 1; x} + {x = x * 2; x}

  } ensuring(res => res == 18)

}
