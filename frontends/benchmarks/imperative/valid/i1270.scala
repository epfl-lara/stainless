object i1270 {
  case class Box(var value: Int)

  def outer(b: Box): Unit = {
    def inner(v: Int): Unit = {
      require(b.value == v)
    }
    inner(b.value)
  }
}