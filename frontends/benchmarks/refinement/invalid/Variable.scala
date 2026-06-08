package variable2

object A:
  def f() =
    var x: Int = 1
    def foo() = x
    var y : { y: Int with y == foo() } = 1
    x = 2
    y = y // re-type check with new value of y
