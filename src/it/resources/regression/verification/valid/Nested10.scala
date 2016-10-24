/* Copyright 2009-2016 EPFL, Lausanne */

object Nested10 {

  def foo(i: Int): Int = {
    val n = 2
    def rec1(j: Int) = {
      i + j + n
    }
    def rec2(j: Int) = {
      rec1(j)
    }
    rec2(2)
  } ensuring(i + 4 == _)

}
