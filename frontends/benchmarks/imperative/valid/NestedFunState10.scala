import stainless.lang._

object NestedFunState10 {

  def foo(): Unit = {

    var i = 0

    def getI = i

    (while(i < 10) {
      i += 1
    }) invariant(getI >= 0)

    assert(i == 10)
  }

}
