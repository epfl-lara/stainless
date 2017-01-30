/* Copyright 2009-2016 EPFL, Lausanne */

object IfExpr1 {

  def foo(): Int = {
    var a = 1
    var b = 2
    if({a = a + 1; a != b})
      a = a + 3
    else
      b = a + b
    a
  } ensuring(_ == 3)

}
