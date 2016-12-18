/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object ArrayNested1 {

  def test(): Int = {

    var a = Array(1, 2, 0)

    def nested(): Unit = {
      require(a.length == 3)
      a = a.updated(1, 5)
    }

    nested()
    a(1)

  } ensuring(_ == 5)

}
