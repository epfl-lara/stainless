/* Copyright 2009-2021 EPFL, Lausanne */

object Nested16 {

  def foo(i: BigInt): BigInt = {
    def rec1(j: BigInt): BigInt = {
      require(j >= 0)
      def rec2(k: BigInt): BigInt = {
        require(j > 0 || j == k)
        if(k == 0) 0 else rec1(j-1)
      }
      rec2(j)
    }
    rec1(3)
  } ensuring(0 == _)

}
