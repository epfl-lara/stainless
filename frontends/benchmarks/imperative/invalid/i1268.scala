object i1268 {
  case class Box(var value: Int)

  def outer(cond: Boolean): Unit = {
    val box = Box(123)
    assert(box.value == 123)

    def inner: Unit = {
      assert(box.value == 123) // invalid (though we never actually call inner)
    }

    if (cond) box.value = 456
  }
}