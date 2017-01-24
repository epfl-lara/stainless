/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object NestedFunState3 {


  def counterN(n: Int): Int = {
    require(n > 0)

    var counter = 0

    def inc(): Unit = {
      counter += 1
    }

    var i = 0
    (while(i < n) {
      inc()
      i += 1
    }) invariant(i >= 0 && counter == i && i <= n)

    counter
  } ensuring(_ == n)

}
