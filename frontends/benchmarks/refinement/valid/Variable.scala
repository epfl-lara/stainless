package variable

object A:
  def f() =
    var x: Int = 1
    def foo() = x
    val y : { y: Int with y == foo() } = 1
    x = 2
    assert(y != x)