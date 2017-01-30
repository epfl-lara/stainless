/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._
import stainless.collection._
import stainless._

object BVDivisionByZero2 {

  def division(x: Int, y: Int): Int = {
    require(y != 0)
    x / y
  }
  
}
