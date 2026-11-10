import stainless.lang._

object EarlyReturnInBranch {
  case class Box(var value: BigInt)

  def f(cond: Boolean): Unit = {
    var a = Box(4)
    var b = a

    if (cond) {
      assert(b.value == 4)
      return
    }
    a.value = 99

    assert(b.value == 99)
  }
}
