/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._
import stainless.collection._
import stainless._

object ShortCircuit {

  def negate(a: Boolean) = {
    var b = true
    a && { b = false; true }
    b
  } ensuring { res => res != a }

  def negateOr(a: Boolean) = {
    var b = false
    a || { b = true; true }
    b
  } ensuring { res => res != a }

}
