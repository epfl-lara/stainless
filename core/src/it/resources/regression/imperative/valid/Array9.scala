object Array9 {

  def g(a: Array[Int]): Array[Int] = {
    require(a.length > 0)
    a.updated(0, 10)
  }

  def test(): Int = {
    val b = Array(1,2,3,4)
    val c = g(b)
    c(0)
  } ensuring(_ == 10)

}
