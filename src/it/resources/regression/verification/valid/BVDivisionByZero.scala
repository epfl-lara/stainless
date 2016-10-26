/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._
import stainless.collection._
import stainless._

object BVDivisionByZero {

  def noDivByZero(x: Int): Boolean = {
    (x / 10 == 10)
  }

  def noRemByZero(x: BigInt): Boolean = {
    (x % 10 == 10)
  }
  
}
