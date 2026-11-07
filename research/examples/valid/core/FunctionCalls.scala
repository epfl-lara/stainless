import stainless.lang._

object FunctionCalls {
  case class Box(var value: BigInt)
  case class Holder(var b: Box)

  def mutate(h: Holder): Unit = {
    h.b.value = 3
  }

  def pick(h: Holder): Box = h.b

  def update(h: Holder, a: Box): Unit = {
    h.b = a
  }

  def f: Unit = {
    val h = Holder(Box(1))

    mutate(h)
    val q = pick(h)
    update(h, Box(2))

    assert(q.value == 3)
    assert(h.b.value == 2)
  }
}
