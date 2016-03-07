/* Copyright 2009-2016 EPFL, Lausanne */

object Nested7 {

  def foo(a: BigInt): BigInt = {
    require(a >= 0)
    val b = a + 2
    def rec1(c: BigInt): BigInt = {
      require(c >= 0)
      b + c + bar(a) + bar(b) + bar(c)
    }
    rec1(2) + bar(a)
  } ensuring(_ > 0)


  def bar(x: BigInt): BigInt = {
    require(x >= 0)
    x
  } ensuring(_ >= 0)

}
