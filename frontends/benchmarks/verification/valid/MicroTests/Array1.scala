/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._

object Array1 {

  def foo(a: Array[Int]): Int = {
    require(a.length > 2 && a(2) == 5)
    a(2)
  } ensuring(_ == 5)

  def bar(): Int = {
    val a = Array.fill(5)(5)
    foo(a)
  }

}
