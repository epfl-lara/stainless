/* Copyright 2009-2016 EPFL, Lausanne */

object Nested6 {

  def foo(a: BigInt): BigInt = {
    require(a >= 0)
    def bar(b: BigInt): BigInt = {
      require(b > 0)
      b + 3
    } ensuring(prop(a, b) && a >= 0 && _ == b + 3)
    bar(2)
  } ensuring(a >= 0 && _ == BigInt(5))

  def prop(x: BigInt, y: BigInt): Boolean = x + y > 0

}
