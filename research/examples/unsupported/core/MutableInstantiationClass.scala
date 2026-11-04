import stainless.lang._

object MutableInstantiationClass {
  case class Box(var value: BigInt)
  case class Wrap[T](v: T)

  def unwrap[T](w: Wrap[T]): T = w.v

  def f(c: Boolean, a: Box, b: Box): Unit = {
    val w = if (c) Wrap(a) else Wrap(b)
    val m = unwrap(w)

    m.value = 1

    assert(if (c) a.value == 1 else b.value == 1)
  }
}
