import stainless.lang._

object LoopWriteThenMutateAlias {
  case class Box(var value: BigInt)

  def f(a: Array[Box]): Unit = {
    require(a.length > 2)

    val x = a(0)

    var i = 0
    (while (i < a.length) {
      decreases(a.length - i)
      a(i) = Box(1)
      i += 1
    }).invariant(0 <= i && i <= a.length && a.length > 2)

    x.value = 5

    assert(a(0).value == 5)
  }
}
