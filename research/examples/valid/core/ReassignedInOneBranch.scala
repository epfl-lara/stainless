import stainless.lang._

object ReassignedInOneBranch {
  case class Box(var value: BigInt)

  def f(cond: Boolean): Unit = {
    var x = Box(1)
    val b = x
    if (cond) {
      x = Box(2)
    }

    x.value = 3

    assert(if (cond) b.value == 1 else b.value == 3)
  }
}
