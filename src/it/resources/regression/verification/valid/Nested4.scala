/* Copyright 2009-2016 EPFL, Lausanne */

object Nested4 {

  def foo(a: BigInt, a2: BigInt): BigInt = {
    require(a >= 0 && a <= 50)
    val b = a + 2
    val c = a + b
    if(a2 > a) {
      def rec1(d: BigInt): BigInt = {
        require(d >= 0 && d <= 50)
        val e = d + b + c + a2
        e
      } ensuring(_ > 0)
      rec1(2)
    } else {
      BigInt(5)
    }
  } ensuring(x => x > 0)

}
