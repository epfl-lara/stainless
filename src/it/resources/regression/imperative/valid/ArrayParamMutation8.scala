/* Copyright 2009-2015 EPFL, Lausanne */

import stainless.lang._

object ArrayParamMutation8 {

  def odd(a: Array[BigInt]): Boolean = {
    require(a.length > 0 && a(0) >= 0)
    if(a(0) == 0) false
    else {
      a(0) = a(0) - 1
      even(a)
    }
  } ensuring(res => if(old(a)(0) % 2 == 1) res else !res)

  def even(a: Array[BigInt]): Boolean = {
    require(a.length > 0 && a(0) >= 0)
    if(a(0) == 0) true
    else {
      a(0) = a(0) - 1
      odd(a)
    }
  } ensuring(res => if(old(a)(0) % 2 == 0) res else !res)

}
