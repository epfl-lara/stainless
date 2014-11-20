import leon.lang._

object Lambdas {
  def gen(x: Int): (Int) => Int = {
    val f = (x: Int) => x + 1
    val g = (x: Int) => x + 2
    if (x > 0) g else f
  }

  def test(x: Int): Boolean = {
    require(x > 0)
    val f = gen(x)
    f(x) == x + 2
  }.holds
}
