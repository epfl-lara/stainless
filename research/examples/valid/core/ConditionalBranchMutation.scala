import stainless.lang._

object ConditionalBranchMutation {
  case class Box(var value: BigInt)

  def f(cond: Boolean): Unit = {
    var a = Box(4)
    var b = a

    if (cond) {
      a.value = 5
    }

    assert(if (cond) b.value == 5 else b.value == 4)
  }
}
