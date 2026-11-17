import stainless.lang._

object LocalSharedResult {
  case class Box(var value: BigInt)


  def f(): Unit = {
    def mk(): (Box, Box) = { val n = Box(1); (n, n) }
    val r = mk()
    r._1.value = 5
    assert(r._2.value == 5)
  }
}
