/* Copyright 2009-2016 EPFL, Lausanne */

object Nested5 {

  def foo(a: Int): Int = {
    require(a >= 0)
    def bar(b: Int): Int = {
      require(b > 0)
      b + 3
    } ensuring(a >= 0 && _ == b + 3)
    bar(2)
  } ensuring(a >= 0 && _ == 5)

}
