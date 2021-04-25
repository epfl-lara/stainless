/* Copyright 2009-2021 EPFL, Lausanne */

object AddingPositiveNumbers {

  //this should overflow with bit vectors
  def additionOverflow(x: Int, y: Int): Int = {
    require(x >= 0 && y >= 0)
    x + y
  } ensuring(_ >= 0)

}
