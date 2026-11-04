import stainless.lang._

object FieldOperandOrder {
  case class Box(var value: BigInt)

  def f: Unit = {
    val b = Box(0)

    val r = b.value + { b.value = 1; b.value }

    assert(r == 2)
  }
}
