import stainless.lang._

object FieldWriteInBranchThenMutateAlias {
  case class Box(var value: BigInt)
  case class Holder(var b: Box)

  def f(h: Holder, c: Boolean): Unit = {
    val y = h.b
    if (c) h.b = Box(1)

    y.value = 2

    assert(h.b.value == 2)
  }
}
