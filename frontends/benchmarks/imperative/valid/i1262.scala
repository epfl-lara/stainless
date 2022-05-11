object i1262 {
  case class Box(var length: Int)
  def makeBox(): Box = Box(0)

  def f(b: Box): Unit = {
    val c =
      if (true) b
      else makeBox()
    c.length = 1
  }

  def mutate(b: Box): Unit = { b.length = 123; }

  def g(b1: Box, b2: Box): Unit = {
    val oldB2 = b2.length
    val c = if (true) b1 else b2
    mutate(c)
    assert(c.length == 123)
    assert(b1.length == 123)
    assert(b2.length == oldB2)
  }

  def h(b1: Box, b2: Box): Unit = {
    val oldB2 = b2.length
    val c = if (true) b1 else b2
    val d = c // Interacts with Let handling `computeExprEffects`
    mutate(d)
    assert(c.length == 123)
    assert(b1.length == 123)
    assert(d.length == 123)
    assert(b2.length == oldB2)
  }
}