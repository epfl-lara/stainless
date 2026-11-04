import stainless.lang._

object ConditionalInitialAliasWrong {
  case class Box(var value: BigInt)

  def f(cond: Boolean): Unit = {
    val c = Box(0)
    val d = Box(1)
    var a = if (cond) c else d

    a.value = 5
    c.value = 0

    assert(a.value == 5)
  }
}
