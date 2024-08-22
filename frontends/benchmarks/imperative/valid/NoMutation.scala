import stainless.lang._

object test {
  case class Test(var value: Int)

  def stuff(x: Test): Unit = ()

  def test(x: Test) = {
    stuff(x)
    x.value
  }.ensuring { _ == old(x).value }

}
