import stainless.lang._

object FieldArrayReplacedThenMutateAlias {
  case class Box(var value: BigInt)
  case class Store(var arr: Array[Box])

  def f(s: Store): Unit = {
    require(s.arr.length > 0)

    val x = s.arr(0)
    s.arr = Array(Box(9))

    x.value = 1

    assert(s.arr(0).value == 1)
  }
}
