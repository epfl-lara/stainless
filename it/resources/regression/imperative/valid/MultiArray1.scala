object MultiArray1 {

  def test: Int = {

    val b: Array[Array[Int]] = Array.fill(10)(Array.fill(10)(0))

    b(0)(0)
  } ensuring(_ == 0)

}
