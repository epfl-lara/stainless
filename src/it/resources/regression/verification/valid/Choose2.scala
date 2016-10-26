/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._
import stainless.lang.synthesis._

object Choose2 {

  def test(x: Int): Int = {

    choose((y: Int) => {
      val z = y + 2
      z == y
    })

  } ensuring(_ == x + 2)

}
