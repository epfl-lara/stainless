import stainless.lang._

object EarlyReturnInCalleeWrong {
  case class Box(var value: BigInt)
  case class Holder(var a: Box, var b: Box)

  def setBoth(p: Holder, c: Boolean): Unit = {
    if (c) {
      val n = Box(1)
      p.a = n
      p.b = n
      return ()
    }
  }

  def f(p: Holder, c: Boolean): Unit = {
    setBoth(p, c)
    p.a.value = 5

    assert(p.b.value == 5)
  }
}
