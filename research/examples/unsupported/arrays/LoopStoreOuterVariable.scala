import stainless.lang._

object LoopStoreOuterVariable {
  case class Box(var value: BigInt)

  def f(a: Array[Box]): Unit = {
    val x = Box(1)

    var i = 0
    (while (i < a.length) {
      decreases(a.length - i)
      a(i) = x
      i += 1
    }).invariant(0 <= i && i <= a.length)
  }
}
