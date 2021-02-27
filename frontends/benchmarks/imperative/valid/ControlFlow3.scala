import stainless.lang._

object ControlFlow3 {
  def bar(x: Option[Int]): Int = {
    if (x.isEmpty) {
      return 1
    }

    var y: Int = 0

    (while (y < 10) {
      decreases(10 - y)
      if (y == x.get) {
        return y
      }

      y += 1
    }).invariant(0 <= y && y <= 10)

    y
  }

  def testBar: Unit = {
    assert(bar(None()) == 1)
    assert(bar(Some(5)) == 5)
    assert(bar(Some(20)) == 10)
  }
}
