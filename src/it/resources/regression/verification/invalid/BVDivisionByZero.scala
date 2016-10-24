/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.collection._
import leon._

object BVDivisionByZero {

  def divByZero(x: Int): Boolean = {
    (x / 0 == 10)
  }
  
}
