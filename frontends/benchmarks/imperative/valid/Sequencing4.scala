/* Copyright 2009-2019 EPFL, Lausanne */

object Sequencing4 {

  def test(): Int = {
    var x = 5

    {x = x + 1; x} + {x = x * 2; x}

  } ensuring(res => res == 18)

}
