/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object ChooseLIA {

  def test(x: BigInt): BigInt = {

    choose((y: BigInt) => {
      val z = x + 2
      z == y
    })

  } ensuring(_ == x + 2)

}
