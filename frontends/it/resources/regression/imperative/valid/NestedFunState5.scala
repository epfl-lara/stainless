/* Copyright 2009-2016 EPFL, Lausanne */

import stainless.lang._

object NestedFunState5 {

  def deep(n: BigInt): BigInt = {
    require(n > 0)

    var a = BigInt(0)

    def iter(prevA: BigInt): Unit = {
      require(prevA == a)
      def nestedIter(): Unit = {
        a += 1
      }

      nestedIter()
      nestedIter()

    } ensuring(_ => a == prevA + 2)

    var i = BigInt(0)
    (while(i < n) {
      i += 1
      iter(a)
    }) invariant(i >= 0 && i <= n && a >= 2*i)

    a
  } ensuring(_ >= 2*n)
}
