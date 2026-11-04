import stainless.lang._

object UpdatedWhileBoundWrong {
  case class Box(var value: BigInt)

  def f(k: BigInt): Unit = {
    var m = MutableMap.withDefaultValue[BigInt, Box](() => Box(0))
    val x = m(k)

    m = m.updated(0, Box(9))
    x.value = 5
  }
}
