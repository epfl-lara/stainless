object ExploratoryTest {
  val y = (1, 2)
  val b = 1 -> 2
//
//  def test(fun: Int => Int): Int =  fun(3)
//
//  def div(x: Short, y: Short): Short = {
////    def testFunction(z: Int): Int = z / y
//    (x / y).toShort
//  }

  def checkIf(x: Long, y: Long): Long = {
    if (x <= y)
      x
    else
      b._1 / b._2
  }
}