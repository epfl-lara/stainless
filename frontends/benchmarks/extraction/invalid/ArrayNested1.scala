/* Copyright 2009-2021 EPFL, Lausanne */

import stainless.lang._

// FIXME: Used to be accepted and verified (now rejected at extraction)
object ArrayNested1 {

  def test(): Int = {
    // Cannot var-bind a mutable type
    var a = Array(1, 2, 0)

    def nested(): Unit = {
      require(a.length == 3)
      a = a.updated(1, 5)
    }

    nested()
    a(1)

 }.ensuring(_ == 5)

}
