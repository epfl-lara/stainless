import stainless.annotation._

object Purity2 {

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
