/* Copyright 2009-2016 EPFL, Lausanne */

object Array1 {

  def foo(): Int = {
    val a = Array.fill(5)(0)
    a(2) = 3
    a(2)
  } ensuring(_ == 0)

}
