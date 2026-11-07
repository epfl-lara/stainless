import stainless.lang._

object MapLoopWriteThenMutateAlias {
  case class Box(var value: BigInt)

  def f(m: MutableMap[BigInt, Box]): Unit = {
    val x = m(0)

    var i = BigInt(0)
    (while (i < 3) {
      decreases(3 - i)
      m(i) = Box(1)
      i += 1
    }).invariant(0 <= i && i <= 3)

    x.value = 5

    assert(m(0).value == 5)
  }
}
