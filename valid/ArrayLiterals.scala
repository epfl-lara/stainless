/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._
object Numerals {
  def foo(): Int = {
    val b : Array[Int] = Array[Int](1,2,3)
    val a : Array[Int] = Array(1,2,3)
    a.length
  } ensuring { _ > 0 }
}
