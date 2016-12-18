/* Copyright 2009-2016 EPFL, Lausanne */

object Assign1 {

  def foo(): Int = {
    var a = 0
    val tmp = a + 1
    a = a + 2
    a = a + tmp
    a = a + 4
    a
  } ensuring(_ == 7)

}
