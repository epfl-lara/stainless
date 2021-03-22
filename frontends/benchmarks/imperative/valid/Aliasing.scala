object UnsupportedAlias {
  case class B(var i: BigInt)
  case class A(var b: B)

  def test(): Unit = {
    val b = B(0)
    val a = A(b)
    a.b = B(1)
    assert(a.b.i == 1)
  }
}
