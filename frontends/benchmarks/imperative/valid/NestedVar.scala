/* Copyright 2009-2016 EPFL, Lausanne */

object NestedVar {

  def foo(): Int = {
    val a = 3
    def rec(x: Int): Int = {
      var b = 3
      var c = 3
      if(x > 0)
        b = 2
      else
        c = 2
      c+b
    }
    rec(a)
  } ensuring(_ == 5)

}
