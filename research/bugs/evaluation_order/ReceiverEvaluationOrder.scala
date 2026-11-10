import stainless.lang._

object ReceiverEvaluationOrder {
  case class Box(var value: BigInt)
  case class Holder(var b: Box)

  def f: Unit = {
    val h = Holder(Box(1))

    h.b.value = { h.b = Box(7); 1 }

    assert(h.b.value == 1)
  }
}
