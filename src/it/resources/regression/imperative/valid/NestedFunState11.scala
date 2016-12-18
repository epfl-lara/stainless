import stainless.lang._

object NestedFunState11 {

  def foo(): Unit = {

    var i = 0

    def getI = i

    def rec(): Unit = {
      require(getI >= 0)
      if(i < 10) {
        i += 1
        rec()
      }
    } ensuring(_ => getI >= 0)

    rec()

    assert(i == 10)
  }

}
