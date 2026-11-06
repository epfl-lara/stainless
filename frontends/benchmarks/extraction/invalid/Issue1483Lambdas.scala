object i1483c {
  case class A(l: BigInt => BigInt)

  def test: Unit = {
    val a1 = A(_ + 1)
    val a2 = A(_ + 1)
    // true for Stainless, but false at runtime
    assert(a1 == a2)
  }
}

object i1483f {
  case class Wrapper(l: BigInt => BigInt)
  case class A[T](t: T)

  def test: Unit = {
    val a1 = A(Wrapper(_ + 1))
    val a2 = A(Wrapper(_ + 1))
    // true for Stainless, but false at runtime
    assert(a1 == a2)
  }
}
