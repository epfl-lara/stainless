object MultiArray5 {

  def foo(b: Array[Array[Int]]): Int = {
    require(b.length >= 10 && b(2).length >= 10)
    b(2)(3) = 13
    b(2)(3)
  } ensuring(_ == 13)


  def test: Int = {
    val a: Array[Array[Int]] = Array.fill(10)(Array.fill(10)(0))
    foo(a)
    a(2)(3)
  } ensuring(_ == 13)


}
