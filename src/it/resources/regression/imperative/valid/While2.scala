/* Copyright 2009-2016 EPFL, Lausanne */

object While2 {

  def foo(): Int = {
    var a = 0
    var i = 0
    while(i < 10) {
      a = a + i
      i = i + 1
    }
    a
  } ensuring(_ == 45)

}
