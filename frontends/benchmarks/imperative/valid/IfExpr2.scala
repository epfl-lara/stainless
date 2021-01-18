/* Copyright 2009-2021 EPFL, Lausanne */
import stainless.annotation._

object IfExpr2 {

  def foo(): Int = {
    var a = 1
    var b = 2
    if(a < b) {
      a = a + 3
      b = b + 2
      a = a + b
    }
    a
  } ensuring(_ == 8)

}
