import stainless.lang._

object CollapsedConditionWrite {
  case class Box(var value: BigInt)
  case class Holder(var b: Box)

  def make(c: Boolean): (Holder, Box) = {
    val x = Box(0)
    val y = Box(1)

    (Holder(if (c) x else y), if (c) y else x)
  }

  def f(c: Boolean): Unit = {
    val (h, _) = make(c)

    h.b.value = 7

    assert(h.b.value == 7)
  }
}
