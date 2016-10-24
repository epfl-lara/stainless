/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._

object Nested8 {

  def foo(a: BigInt): BigInt = {
    require(a > 0)

    def bar(b: BigInt): BigInt = {
      if(a < b) {
        def rec(c: BigInt): BigInt = {
          require(c > 0)
          c + b
        } ensuring(_ > 0)
        rec(2)
      } else 3
    }
    bar(1)
  } ensuring(_ > 0)

  /*
  def partitioned(a: Map[Int, Int], size: Int, l1: Int, u1: Int, l2: Int, u2: Int): Boolean = {
    require(l1 >= 0 && u1 < l2 && u2 < size)
    if(l2 > u2 || l1 > u1)
      true
    else {
      var i = l1
      var j = l2
      var isPartitionned = true
      (while(i <= u1) {
        j = l2
        (while(j <= u2) {
          if(a(i) > a(j))
            isPartitionned = false
          j = j + 1
        }) invariant(j >= l2 && i <= u1)
        i = i + 1
      }) invariant(i >= l1)
      isPartitionned
    }
  }
  */

}
