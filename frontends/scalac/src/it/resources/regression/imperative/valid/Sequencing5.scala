/* Copyright 2009-2016 EPFL, Lausanne */

object Sequencing5 {


  def test(): (Int, Int, Int) = {
    var x = 5

    (
      {x = x + 1; x},
      {x = x * 2; x},
      {x = x - 1; x}
    )

  } ensuring(res => res._1 == 6 && res._2 == 12 && res._3 == 11)

}
