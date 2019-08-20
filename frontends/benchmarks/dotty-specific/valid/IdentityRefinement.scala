
object IdentityRefinement {
  type Neg = { x: Int => x < 0 }

  def id[T](x: T): T = x

  def f() = id[{x: Int => x > 0}](1) + id[Neg](-1)
}

