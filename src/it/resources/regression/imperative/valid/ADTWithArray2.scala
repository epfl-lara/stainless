object ADTWithArray2 {

  case class A(a: Array[Int], size: Int)

  def foo(a: A): Unit = {
    require(a.a.length > 0 && a.a.length == a.size)
    a.a(0) = 10
  }

  def test(): Int = {
    val a = A(Array(1,2,3), 3)
    foo(a)
    a.a(0)
  } ensuring(_ == 10)

}
