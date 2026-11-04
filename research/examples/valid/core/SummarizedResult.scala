import stainless.lang._

object SummarizedResult {
  case class Box(var value: BigInt)
  case class Holder(b: Box)

  def get(h: Holder): Box = h.b

  def f(a: Box): Unit = {
    val h = Holder(a)
    val m = get(h)

    m.value = 1

    assert(a.value == 1)
  }
}
