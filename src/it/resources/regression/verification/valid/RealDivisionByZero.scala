/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.collection._
import leon._

object RealDivisionByZero {

  def noDivByZero(x: Real): Boolean = {
    (x / Real(10) == Real(10))
  }
  
}
