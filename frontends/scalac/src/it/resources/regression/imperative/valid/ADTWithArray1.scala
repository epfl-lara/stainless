object ADTWithArray1 {

  case class A(a: Array[Int])

  def foo(a: A): Unit = {
    require(a.a.length > 0)
    a.a(0) = 10
  }

  def test(): Int = {
    val a = A(Array(1,2,3))
    foo(a)
    a.a(0)
  } ensuring(_ == 10)

}
