object ADTWithArray3 {

  case class A(var x: Int)
  case class B(a: Array[A])

  def foo(b: B): Unit = {
    require(b.a.length > 0)
    b.a(0).x = 12
  }

  def test(): B = {
    val b = B(Array(A(1),A(2),A(3)))
    foo(b)
    b
  } ensuring(b => b.a(0).x == 12)

}
