import stainless.lang._

object WriteWhileBoundWrong {
  case class Box(var value: BigInt)

  def f(a: Array[Box], i: Int, k: Int): Unit = {
    require(0 <= i && i < a.length && 0 <= k && k < a.length)

    val y = a(k)

    a(i) = Box(3)
    y.value = 1
  }
}
