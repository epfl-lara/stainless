/* Copyright 2009-2021 EPFL, Lausanne */
import stainless.annotation._
import stainless.lang._

object While1 {

  def foo(): Int = {
    var a = 0
    var i = 0
    (while(i < 10) {
      decreases(10 - i)
      a = a + 1
      i = i + 1
    }).invariant(i >= 0)
    a
  }.ensuring(_ == 10)

}
