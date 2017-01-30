/* Copyright 2009-2016 EPFL, Lausanne */

package stainless.lang
import stainless.annotation._

@ignore
class Real {

   def +(a: Real): Real = ???
   def -(a: Real): Real = ???
   def *(a: Real): Real = ???
   def /(a: Real): Real = ???

   def unary_- : Real = ???

   def > (a: Real): Boolean = ???
   def >=(a: Real): Boolean = ???
   def < (a: Real): Boolean = ???
   def <=(a: Real): Boolean = ???

}

@ignore
object Real {
  def apply(n: BigInt, d: BigInt): Real = ???
  def apply(n: BigInt): Real = ???
}
