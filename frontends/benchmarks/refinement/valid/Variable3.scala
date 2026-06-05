package variable3
import language.experimental.qualifiedTypes.silent

object A:
  def f() =
    var x: Int = 1
    def foo() = x
    def bar() : {r : Int with r == foo()} = foo()