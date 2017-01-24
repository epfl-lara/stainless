/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object NestedFunState7 {

  def test(x: BigInt): BigInt = {

    var a = BigInt(0)

    def defCase(): Unit = {
      a = 100
    }

    if(x >= 0) {
      a = 2*x
      if(a < 100) {
        a = 100 - a
      } else {
        defCase()
      }
    } else {
      defCase()
    }

    a
  } ensuring(res => res >= 0 && res <= 100)

}
