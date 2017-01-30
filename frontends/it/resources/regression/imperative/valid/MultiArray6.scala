object MultiArray6 {

  def foo(b: Array[Int]): Int = {
    require(b.length >= 10)
    b(3) = 13
    b(3)
  } ensuring(_ == 13)


  def test: Int = {
    val a: Array[Array[Int]] = Array.fill(10)(Array.fill(10)(0))
    foo(a(2))
    a(2)(3)
  } ensuring(_ == 13)


}
