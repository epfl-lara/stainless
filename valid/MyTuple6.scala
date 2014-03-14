/* Copyright 2009-2014 EPFL, Lausanne */

object MyTuple6 {

  def foo(t: (Int, Int)): (Int, Int) = {
    require(t._1 > 0 && t._2 > 1)
    t
  } ensuring(res => res._1 > 0 && res._2 > 1)

}
