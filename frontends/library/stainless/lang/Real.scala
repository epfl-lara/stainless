/* Copyright 2009-2018 EPFL, Lausanne */

package stainless.lang
import stainless.annotation._

import scala.language.implicitConversions

@ignore
class Real(val theReal: scala.math.BigDecimal) {

   def +(a: Real): Real = new Real(theReal + a.theReal)
   def -(a: Real): Real = new Real(theReal - a.theReal)
   def *(a: Real): Real = new Real(theReal * a.theReal)
   def /(a: Real): Real = new Real(theReal / a.theReal)

   def unary_- : Real = new Real(- theReal)

   def > (a: Real): Boolean = theReal >  a.theReal
   def >=(a: Real): Boolean = theReal >= a.theReal
   def < (a: Real): Boolean = theReal <  a.theReal
   def <=(a: Real): Boolean = theReal <= a.theReal

}

@ignore
object Real {
  def apply(n: BigInt, d: BigInt): Real = new Real(scala.math.BigDecimal(n) / scala.math.BigDecimal(d))
  def apply(n: BigInt): Real = new Real(scala.math.BigDecimal(n))
}
