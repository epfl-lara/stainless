package variable2
import language.experimental.qualifiedTypes.silent

object A:
  def f() =
    var x: Int = 1
    def foo() = x
    var y : { y: Int with y == foo() } = 1
    x = 2
    y = 2 // re-type check with new value of y
    assert(y == x)