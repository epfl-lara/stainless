import stainless.lang._

object NestedFunState9 {
  def test() = {
    var c = 0

    def foo(x: Int) = {
      require(c == 8)
      x
    }

    c = c+8
    foo(c)

  } ensuring(_ == 8)
}
