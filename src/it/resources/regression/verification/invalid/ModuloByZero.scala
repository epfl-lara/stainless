/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.collection._
import leon._

object ModuloByZero {

  def modByZero(x: BigInt): Boolean = {
    (x mod BigInt(0)) == BigInt(10)
  }

}
