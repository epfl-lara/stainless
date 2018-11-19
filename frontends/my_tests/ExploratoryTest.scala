//import stainless.lang.Bag

object ExploratoryTest {

//  val f2 = (x: Int) => x / 2
//

  def checkIf(x: Int, y: Int): Int = {
    val b = 1 -> 2
    val f2 = (x: Int) => x / y
    if (x <= y)
      f2(x)
    else
      b._1 / b._2
  }
}