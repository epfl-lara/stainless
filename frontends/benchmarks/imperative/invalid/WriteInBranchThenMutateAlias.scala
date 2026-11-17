import stainless.lang._

object WriteInBranchThenMutateAlias {
  case class Box(var value: BigInt)

  def f(a: Array[Box], i: Int, c: Boolean): Unit = {
    require(0 <= i && i < a.length)

    val x = a(i)
    if (c) a(i) = Box(1)

    x.value = 2

    assert(a(i).value == 2)
  }
}
