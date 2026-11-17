import stainless.lang._

object ConditionalInitialAlias {
  case class Box(var value: BigInt)

  def f(cond: Boolean): Unit = {
    var a = if (cond) Box(4) else Box(9)
    var b = a

    a.value = 5

    assert(b.value == 5)
  }
}
