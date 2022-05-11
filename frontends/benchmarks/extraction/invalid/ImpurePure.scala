import stainless.annotation.pure

object ImpurePure {
  case class Box(var length: Int)
  def makeBox(): Box = Box(0)

  @pure def f(b: Box): Unit = { // A lying "pure" function!
    val c =
      if (true) b
      else makeBox()
    c.length = 1
  }

  def mutate(b: Box): Unit = { b.length = 123; }

  def g(b1: Box, b2: Box): Unit = {
    val c = if (true) b1 else b2
    mutate(c)
  }

  def h(b1: Box, b2: Box): Unit = {
    val c = if (true) b1 else b2
    val d = c // Interacts with Let handling `computeExprEffects`
    mutate(d)
  }
}