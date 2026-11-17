import stainless.lang._

object WriteWhileBoundKeyWrong {
  case class Box(var value: BigInt)

  def f(m: MutableMap[BigInt, Box], j: BigInt, k: BigInt): Unit = {
    val y = m(k)

    m(j) = Box(3)
    y.value = 1
  }
}
