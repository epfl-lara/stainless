import stainless.lang._

object WriteAtEqualIndexThenMutateAlias {
  case class Box(var value: BigInt)

  def f(j: Int): Unit = {
    require(0 <= j && j < 2)

    val a = Array(Box(0), Box(0))
    val x = a(0)
    a(j) = Box(5)

    x.value = 1

    assert(j == 0 || a(0).value == 1)
    assert(j != 0 || a(0).value == 1)
  }
}
