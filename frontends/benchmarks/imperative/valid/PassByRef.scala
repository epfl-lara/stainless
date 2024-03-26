object PassByRef {
  case class Box(var value: BigInt)
  case class Container(b: Box)

  def f2(b: Container): Unit = b.b.value = 3

  def g2(b: Container) = {
    val b0 = b
    f2(b)
    assert(b == b0) // Yes, because `b` and `b0` are aliases
  }
}
