object i1290a {
  case class Box(var value: Int)

  def test: Unit = {
    val b1 = Box(123)
    val b2 = Box(456)

    val b3 = if (b1.value == 123) {
      b1.value = 42
      b2
    } else Box(1)

    // b3 aliases b2

    assert(b1.value == 42) // Ok
    assert(b3.value == 456) // Ok

    b2.value = 5
    assert(b3.value == 456) // Invalid
  }
}