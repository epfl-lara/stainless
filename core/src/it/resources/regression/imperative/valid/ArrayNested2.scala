/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object ArrayNested2 {

  def test(): Int = {

    val a = Array(1, 2, 0)

    def nested(): Unit = {
      require(a.length == 3)
      a(2) = 5
    }

    nested()
    a(2)

  } ensuring(_ == 5)

}
