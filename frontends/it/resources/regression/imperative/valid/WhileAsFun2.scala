/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object WhileAsFun2 {


  def counterN(n: Int): Int = {
    require(n > 0)

    var counter = 0

    def inc(): Unit = {
      counter += 1
    }

    var i = 0
    def rec(): Unit = {
      require(i >= 0 && counter == i && i <= n)
      if(i < n) {
        inc()
        i += 1
        rec()
      } else {
        ()
      }
    } ensuring(_ => i >= 0 && counter == i && i <= n && i >= n)
    rec()


    counter
  } ensuring(_ == n)

}
