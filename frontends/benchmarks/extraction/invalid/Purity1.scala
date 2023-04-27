import stainless.annotation._

object Purity1 {

  case class Test(var abc: Int) {

    @pure
    def ok1(x: Int): Int = x

    @pure
    def bad(x: Int): Int = {
      abc = abc + x
      x
    }
  }
}
