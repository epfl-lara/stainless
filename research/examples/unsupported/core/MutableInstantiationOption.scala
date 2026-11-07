import stainless.lang._

object MutableInstantiationOption {
  case class Box(var value: BigInt)

  def f(b: Box): Unit = {
    val o: Option[Box] = Some(b)
    val m = o.get

    m.value = 1

    assert(b.value == 1)
  }
}
