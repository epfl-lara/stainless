import stainless.lang._

object AliasBeforeLoop {
  case class Box(var value: BigInt)

  def f(n: BigInt): Unit = {
    require(n > 0)

    val x = Box(0)
    var y = x
    var i = BigInt(0)
    while (i < n) {
      decreases(n - i)
      y.value = 1
      y = Box(0)
      i = i + 1
    }

    assert(x.value == 1)
  }
}
