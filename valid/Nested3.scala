/* Copyright 2009-2016 EPFL, Lausanne */

object Nested3 {

  def foo(a: BigInt): BigInt = {
    require(a >= 0 && a <= 50)
    val b = a + 2
    val c = a + b
    def rec1(d: BigInt): BigInt = {
      require(d >= 0 && d <= 50)
      val e = d + b + c
      e
    }
    rec1(2)
  } ensuring(_ > 0)

}
