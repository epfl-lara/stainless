/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.collection._
import leon._

object DivisionByZero {

  def noDivByZero(x: BigInt): Boolean = {
    (x / BigInt(10) == BigInt(10))
  }

  def noRemByZero(x: BigInt): Boolean = {
    (x % BigInt(10) == BigInt(10))
  }
  
  def noModByZero(x: BigInt): Boolean = {
    (x mod BigInt(10)) == BigInt(10)
  }
  
}
