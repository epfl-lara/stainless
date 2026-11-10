import stainless.lang._

object LoopBestElement {
  case class Box(var value: BigInt)

  def f(a: Array[Box]): Unit = {
    require(a.length > 1)

    var best = a(0)
    var i = 1
    (while (i < a.length) {
      decreases(a.length - i)
      if (a(i).value > best.value) best = a(i)
      i += 1
    }).invariant(1 <= i && i <= a.length)

    best.value = 0
  }
}
