object ADTWithArray4 {

  case class A(x: Int)
  case class B(a: Array[A])

  def foo(b: B): Int = {
    require(b.a.length > 0)
    b.a(0).x
  }

  def test(): Int = {
    val b = B(Array(A(1),A(2),A(3)))
    foo(b)
  } ensuring(_ == 1)

}
