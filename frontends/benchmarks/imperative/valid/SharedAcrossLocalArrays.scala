import stainless.lang._

object SharedAcrossLocalArrays {
  case class Box(var value: BigInt)

  def f(i: Int, k: Int, j: Int): Unit = {
    require(0 <= i && i < 2 && k == i && 0 <= j && j < 2)

    val a = Array(Box(0), Box(0))
    val c = Array(Box(0), Box(0))
    val x = Box(1)
    a(i) = x
    c(j) = x
    val y = a(k)

    y.value = 5

    assert(x.value == 5)
    assert(c(j).value == 5)
  }
}
