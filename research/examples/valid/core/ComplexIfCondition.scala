import stainless.lang._

object ComplexIfCondition {
  case class Box(var value: BigInt)

  def f: Unit = {
    var a = Box(4)
    var b = a

    if (a.value > 0) {
      a.value = 5
    }

    assert(b.value == 5)
  }
}
