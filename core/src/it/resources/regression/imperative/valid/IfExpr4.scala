/* Copyright 2009-2016 EPFL, Lausanne */

object IfExpr4 {

  def foo(a: Int): Int = {

    if(a > 0) {
      var a = 1
      var b = 2
      a = 3
      a + b
    } else {
      var a = 3
      var b = 1
      b = b + 1
      a + b
    }
  } ensuring(_ == 5)

}
