/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._

object ArrayLiterals {
  def foo(): Int = {
    val b : Array[Int] = Array[Int](1,2,3)
    val a : Array[Int] = Array(1,2,3)
    a.length
  } ensuring { _ > 0 }
}
