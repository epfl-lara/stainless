import stainless.lang._

object FreshExpr2 {

  def iden(arr: Array[Int]) = arr

  // Recursive functions must return fresh expression
  def counting(i: Int): Array[Int] = {
    require(0 <= i && i <= 10)
    decreases(10 - i)
    if (i < 10) {
      counting(i + 1)
    } else {
      val b = Array.fill(0)(0)
      iden(b) // This is a fresh expression
    }
  }
}