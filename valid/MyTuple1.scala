/* Copyright 2009-2014 EPFL, Lausanne */

object MyTuple1 {

  def foo(): Int = {
    val t = (1, true, 3)
    val a1 = t._1
    val a2 = t._2
    val a3 = t._3
    a3
  } ensuring( _ == 3)

}
