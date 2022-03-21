import stainless._
import stainless.lang._

object i1253 {

  case class Box(var value: Int)

  def mutate(b: Box, v: Int): Unit = {
    b.value = v;
  }

  def f(arr: Array[Box], i: Int): Unit = {
    require(0 <= i && i < 2000)
    require(arr.length >= 3000)

    var ii = i
    ii += 1

    val aliasedElem = arr(ii)
    arr(ii).value = 123

    assert(aliasedElem.value == 123)

    ii += 1
    arr(ii).value = 456
    assert(aliasedElem.value == 123)
  }

  // Same as f, but we use mutate instead
  def g(arr: Array[Box], i: Int): Unit = {
    require(0 <= i && i < 2000)
    require(arr.length >= 3000)

    var ii = i
    ii += 1

    val aliasedElem = arr(ii)
    mutate(arr(ii), 123)

    assert(aliasedElem.value == 123)

    ii += 1
    mutate(arr(ii), 456)
    assert(aliasedElem.value == 123)
  }
}
