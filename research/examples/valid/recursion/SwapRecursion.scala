import stainless.lang._

object SwapRecursion {
  case class Box(var value: BigInt)

  def swap(i: BigInt, a: Box, b: Box): (Box, Box) = {
    require(i >= 0)
    decreases(i)

    if (i == 0) (a, b) else swap(i - 1, b, a)
  }.ensuring(res => (res._1.value == a.value && res._2.value == b.value) || (res._1.value == b.value && res._2.value == a.value))

  def f(n: BigInt): Unit = {
    require(n >= 0)

    val p = Box(1)
    val q = Box(2)
    val (x, _) = swap(n, p, q)

    assert(x.value == 1 || x.value == 2)
  }
}
