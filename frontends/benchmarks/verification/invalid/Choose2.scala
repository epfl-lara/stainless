/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

object Choose2 {

  def test(x: BigInt): BigInt = {
    choose[BigInt]((y: BigInt) => {
      val z = y + 2
      z == y
    })
  }.ensuring(_ == x + 2)

}
