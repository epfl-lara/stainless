/* Copyright 2009-2021 EPFL, Lausanne */

object Array2 {

  def foo(): Int = {
    val a = Array.fill(5)(0)
    a(2) = 3
    a.length
  } ensuring(_ == 5)

}
