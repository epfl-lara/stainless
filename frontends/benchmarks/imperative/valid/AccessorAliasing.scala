case class A(var x: BigInt)
trait B { var a: A }

object AccessorAliasing {
  def test(b: B): Unit = {
    val a = b.a
    val old = b.a.x
    a.x += 1
    b.a.x += 1
    assert(b.a.x == old + 2)
    assert(a == b.a)
  }
}
