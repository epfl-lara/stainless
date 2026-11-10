import stainless.lang._

object ReassignedThenCopied {
  case class Box(var value: BigInt)

  def f(cond: Boolean): Unit = {
    var a = Box(1)
    if (cond) {
      a = Box(2)
    }
    val b = a

    a.value = 5

    assert(b.value == 5)
  }
}
