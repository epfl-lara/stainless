object MultiArray4 {

  def foo(b: Array[Array[Int]]): Int = {
    require(b.length >= 10 && b(2).length >= 10)
    b(2)(3) = 13
    b(2)(3)
  } ensuring(_ == 13)

}
