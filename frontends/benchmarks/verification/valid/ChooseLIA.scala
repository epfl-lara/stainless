/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._

object ChooseLIA {

  def test(x: BigInt): BigInt = {
    choose[BigInt]((y: BigInt) => {
      val z = x + 2
      z == y
    })
  } ensuring(_ == x + 2)

}
