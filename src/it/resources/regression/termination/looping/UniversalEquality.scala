/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._
import stainless.collection._
import stainless._

object test {
  
  def universalEquality(e1: BigInt, e2: BigInt): Boolean = {
    val b = looping_proveEquality(e1, e2)
    e1 == e2
  }.holds
  
  def looping_proveEquality(a: BigInt, b: BigInt): Boolean = {
    looping_proveEquality(a, b)
  } ensuring { res => res == (a == b) && res }

}
