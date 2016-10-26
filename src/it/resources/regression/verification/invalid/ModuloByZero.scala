/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._
import stainless.collection._
import stainless._

object ModuloByZero {

  def modByZero(x: BigInt): Boolean = {
    (x mod BigInt(0)) == BigInt(10)
  }

}
