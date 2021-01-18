/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._
import stainless.collection._
import stainless._

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
  
  def multiplyForFun(x: BigInt): Boolean = {
    (x * BigInt(10)) == BigInt(10)
  }

}
