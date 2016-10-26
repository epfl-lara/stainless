/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._
import stainless.collection._
import stainless._

object RemainderByZero {

  def remByZero(x: BigInt): Boolean = {
    (x % BigInt(0) == BigInt(10))
  }

}
