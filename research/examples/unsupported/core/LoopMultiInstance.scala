import stainless.lang._

object LoopMultiInstance {
  case class Box(var value: BigInt)
  case class Holder(var b: Box)

  def f: Unit = {
    val e = Box(7)
    var a = Holder(Box(1))
    var prev = a
    var i = 0

    while (i < 10) {
      a = Holder(Box(2))
      prev.b.value = 5
      prev = a
      prev.b = e
      i += 1
    }
  }
}
