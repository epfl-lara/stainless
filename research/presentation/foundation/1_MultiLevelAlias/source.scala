// NOT SUPPORTED: "Illegal aliasing: B(a)"
import stainless.lang._
object AliasMultiLevel {
  case class A(var x: Int)
  case class B(var y: A)
  case class C(var z: B)

  def test(): Unit = {
    val a = A(4)
    val b = B(a)
    val c = C(b)

    a.x = 5
    assert(a.x == 5)
    assert(b.y.x == 5)
    assert(c.z.y.x == 5)

    b.y = A(1)
    assert(a.x == 5)
    assert(b.y.x == 1)
    assert(c.z.y.x == 1)

    c.z = B(A(2))
    assert(a.x == 5)
    assert(b.y.x == 1)
    assert(c.z.y.x == 2)
  }
}
