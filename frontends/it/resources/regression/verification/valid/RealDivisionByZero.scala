/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._
import stainless.collection._
import stainless._

object RealDivisionByZero {

  def noDivByZero(x: Real): Boolean = {
    (x / Real(10) == Real(10))
  }
  
}
