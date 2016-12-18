/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object WhileAsFun1 {


  def counterN(n: Int): Int = {
    require(n > 0)

    var i = 0
    def rec(): Unit = {
      require(i >= 0 && i <= n)
      if(i < n) {
        i += 1
        rec()
      } else {
        ()
      }
    } ensuring(_ => i >= 0 && i <= n && i >= n)
    rec()

    i
  } ensuring(_ == n)

}
