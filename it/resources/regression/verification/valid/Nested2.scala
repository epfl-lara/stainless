/* Copyright 2009-2016 EPFL, Lausanne */

object Nested2 {

  def foo(a: BigInt): BigInt = {
    require(a >= 0)
    val b = a + 2
    def rec1(c: BigInt): BigInt = {
      require(c >= 0)
      b + c
    }
    rec1(2)
  } ensuring(_ > 0)

}
