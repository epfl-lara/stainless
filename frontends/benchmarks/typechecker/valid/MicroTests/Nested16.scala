/* Copyright 2009-2019 EPFL, Lausanne */

import stainless.lang._

object Nested16 {

  def foo(i: BigInt): BigInt = {
    def rec1(j: BigInt): BigInt = {
      require(j >= 0)
      decreases(j,1)
      def rec2(k: BigInt): BigInt = {
        require(j > 0 || j == k)
        decreases(j,0)
        if(k == 0) 0 else rec1(j-1)
      }
      rec2(j)
    }
    rec1(3)
  } ensuring(0 == _)

}
