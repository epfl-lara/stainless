/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._
import stainless.collection._
import stainless._

object BVDivisionByZero {

  def divByZero(x: Int): Boolean = {
    (x / 0 == 10)
  }
  
}
