import stainless.lang._

object UpdatedWhileBoundWrong {
  case class Box(var value: BigInt)

  def f(arr: Array[Box], i: Int, j: Int): Unit = {
    require(0 <= i && i < arr.length && 0 <= j && j < arr.length)

    var a = arr
    val x = a(j)

    a = a.updated(i, Box(0))
    x.value = 1
  }
}
