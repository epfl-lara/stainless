/* Copyright 2009-2014 EPFL, Lausanne */

object MyTuple3 {

  def foo(): Int = {
    val t = ((2, 3), true)
    t._1._2
  } ensuring( _ == 3)

}
