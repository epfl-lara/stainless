package variable4
import stainless.lang._

object A:
  def f() =
    var x: BigInt = 1
    def foo() = x
    def bar() : {r : BigInt with r == foo()} = 
      x += 1
      foo()
