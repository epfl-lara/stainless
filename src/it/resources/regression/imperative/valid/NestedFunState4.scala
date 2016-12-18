/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object NestedFunState4 {

  def deep(n: BigInt): BigInt = {
    require(n > 0)

    var a = BigInt(0)

    def iter(): Unit = {
      require(a >= 0)

      var b = BigInt(0)

      def nestedIter(): Unit = {
        b += 1
      } 

      var i = BigInt(0)
      (while(i < n) {
        i += 1
        nestedIter()
      }) invariant(i >= 0 && i <= n && b == i)

      a += b

    } ensuring(_ => a >= n)

    var i = BigInt(0)
    (while(i < n) {
      i += 1
      iter()
    }) invariant(i >= 0 && i <= n && a >= i)

    a
  } ensuring(_ >= n)

}
