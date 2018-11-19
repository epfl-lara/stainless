object ExploratoryTest {
  val y: Long = 0
//
//  def test(fun: Int => Int): Int =  fun(3)
//
//  def div(x: Short, y: Short): Short = {
////    def testFunction(z: Int): Int = z / y
//    (x / y).toShort
//  }

  def checkIf(x: Long): Long = {
    if (x <= y)
      x
    else
      x / y
  }
}