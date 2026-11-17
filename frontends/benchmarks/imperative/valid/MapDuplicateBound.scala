import stainless.lang._

object MapDuplicateBound {
  case class Box(var value: BigInt)

  def f(n: Int): Unit = {
    val m = MutableMap.withDefaultValue[Int, Box](() => Box(0))
    val x = m(n)
    val c = m.duplicate()

    x.value = 5

    assert(x.value == 5)
    assert(c(n).value == 5)
  }
}
