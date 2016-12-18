object MultiArray3 {

  def test: Int = {

    val b: Array[Array[Int]] = Array.fill(10)(Array.fill(10)(0))

    b(2)(3) = 10

    b(2)(3)
  } ensuring(_ == 10)

}
