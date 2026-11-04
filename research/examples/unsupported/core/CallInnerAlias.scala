import stainless.lang._

object CallInnerAlias {
  case class Box(var value: BigInt)
  case class Holder(b: Box)

  def mutate(h: Holder): Unit = {
    h.b.value = 3
  }

  def f: Unit = {
    val h = Holder(Box(1))
    val y = h.b

    mutate(h)

    assert(y.value == 3)
  }
}
