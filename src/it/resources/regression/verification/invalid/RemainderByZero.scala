/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.collection._
import leon._

object RemainderByZero {

  def remByZero(x: BigInt): Boolean = {
    (x % BigInt(0) == BigInt(10))
  }

}
