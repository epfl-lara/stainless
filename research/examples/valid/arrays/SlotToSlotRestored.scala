import stainless.lang._

object SlotToSlotRestored {
  case class Box(var value: BigInt)

  def f(a: Array[Box]): Unit = {
    require(a.length > 1)

    a(0) = a(1)
    a(1) = Box(0)
  }
}
