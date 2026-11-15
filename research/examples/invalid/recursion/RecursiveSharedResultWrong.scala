import stainless.lang._

object RecursiveSharedResultWrong {
  case class Box(var value: BigInt)

  def mk(k: BigInt): (Box, Box) = {
    require(k >= 0)
    decreases(k)
    if (k == 0) {
      val n = Box(1)
      (n, n)
    } else mk(k - 1)
  }

  def f(): Unit = {
    val r = mk(3)
    r._1.value = 5
    assert(r._2.value == 1)
  }
}
