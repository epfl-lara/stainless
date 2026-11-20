import stainless.lang._

object SwapBoxes {
  case class Box(var value: BigInt)

  def f(a: Array[Box], i: Int, j: Int): Unit = {
    require(0 <= i && i < a.length && 0 <= j && j < a.length)

    val t = a(i)

    a(i) = a(j)
    a(j) = t
  }
}
