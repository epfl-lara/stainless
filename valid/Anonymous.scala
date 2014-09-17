import leon.lang._

object Anonymous {
  def test(x: Int) = {
    require(x > 0)
    val i = (a: Int) => a + 1
    i(x) + i(2)
  } ensuring { res => res > 0 }
}
