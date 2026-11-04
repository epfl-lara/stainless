import stainless.lang._

object ConditionalAliasAmbiguousWrong {
  case class Box(var value: BigInt)

  def mutate(b: Box): Unit = {
    b.value = 3
  }

  def f(cond: Boolean): Unit = {
    val x = Box(1)
    val y = Box(2)
    val a = if (cond) x else y
    val b = a

    mutate(a)
    a.value = 5
    b.value = 6

    assert(a.value == 6)
    assert(if (cond) x.value == 6 else y.value == 6)
  }
}
