/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.collection._
import leon._

object BVDivisionByZero2 {

  def division(x: Int, y: Int): Int = {
    require(y != 0)
    x / y
  }
  
}
