import stainless.lang._

object LocalStoreThenMutate {
  case class Box(var value: BigInt)
  case class Holder(var b: Box)

  def f(b: Box): Unit = {
    val h = Holder(Box(0))
    h.b = b

    h.b.value = 1

    assert(b.value == 1)
  }
}
