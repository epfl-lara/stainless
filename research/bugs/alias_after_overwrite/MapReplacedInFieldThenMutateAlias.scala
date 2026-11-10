import stainless.lang._

object MapReplacedInFieldThenMutateAlias {
  case class Box(var value: BigInt)
  case class Store(var map: MutableMap[BigInt, Box])

  def f(s: Store): Unit = {
    val x = s.map(0)
    s.map = MutableMap.withDefaultValue[BigInt, Box](() => Box(0))

    x.value = 1

    assert(s.map(0).value == 1)
  }
}
