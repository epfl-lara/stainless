import stainless.lang._

object LambdaCapturingMutableVal {
  case class Box(var value: BigInt)

  def f: Unit = {
    val a = Box(4)
    val bump = (_: Unit) => { a.value = a.value + 1 }

    bump(())
    bump(())

    assert(a.value == 6)
  }
}
