/* Copyright 2009-2016 EPFL, Lausanne */
import stainless.annotation._

object While1 {

  @pure
  def foo(): Int = {
    var a = 0
    var i = 0
    while(i < 10) {
      a = a + 1
      i = i + 1
    }
    a
  } ensuring(_ == 10)

}
