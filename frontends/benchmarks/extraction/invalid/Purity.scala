import stainless.annotation._

object test {

  case class Test(var abc: Int) {

    @pure
    def ok1(x: Int): Int = x

    // @pure
    def bad(x: Int): Int = {
      abc = abc + x
      x
    }
  }

  @pure
  def hello = {
    var test: Int = 1

    @pure
    def world = {
      test = test + 1
      test
    }

    test
  }

}
