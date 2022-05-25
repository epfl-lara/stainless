object i1268a {
  case class Box(var value: Int)

  def outer: Unit = {
    val box = Box(123)
    assert(box.value == 123)

    def inner: Unit = {
      assert(box.value == 123)
    }
  }
}