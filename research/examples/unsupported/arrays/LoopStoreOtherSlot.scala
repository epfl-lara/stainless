import stainless.lang._

object LoopStoreOtherSlot {
  case class Box(var value: BigInt)

  def f(a: Array[Box]): Unit = {
    require(a.length > 1)

    var i = 1
    (while (i < a.length) {
      decreases(a.length - i)
      a(i) = a(0)
      i += 1
    }).invariant(1 <= i && i <= a.length)
  }
}
