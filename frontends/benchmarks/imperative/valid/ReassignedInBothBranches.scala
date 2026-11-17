import stainless.lang._

object ReassignedInBothBranches {
  case class Box(var value: BigInt)

  def f(cond: Boolean): Unit = {
    var x = Box(1)
    val b = x
    if (cond) {
      x = Box(2)
    } else {
      x = Box(3)
    }

    x.value = 3

    assert(b.value == 1)
  }
}
