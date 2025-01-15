/* Copyright 2009-2021 EPFL, Lausanne */

object MyTuple3 {

  def foo(t: (Int, Int)): (Int, Int) = {
    t
  }.ensuring(res => res._1 > 0 && res._2 > 1)

}
