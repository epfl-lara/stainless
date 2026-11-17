import stainless.lang._

object LocalReturnsParam {
  case class Box(var value: BigInt)


  def f(b: Box): Unit = {
    def id(x: Box): Box = x
    b.value = 1
    val y = id(b)
    y.value = 5
    assert(b.value == 5)
  }
}
