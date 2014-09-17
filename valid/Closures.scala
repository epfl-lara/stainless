import leon.lang._

object Closures {
  def addX(x: Int): Int => Int = {
    (a: Int) => a + x
  }

  def test(x: Int): Boolean = {
    val add1 = addX(1)
    val add2 = addX(2)
    add1(add2(1)) == 4
  }.holds
}

// vim: set ts=4 sw=4 et:
