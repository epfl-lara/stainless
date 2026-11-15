import stainless._
import stainless.lang._

object EffectfulArgumentBeforeIndexWrong {
  case class Box(var value: BigInt)

  def set(k: Int, b: Box): Unit = {
    b.value = 5
  }

  def f(arr: Array[Box]): Unit = {
    require(arr.length > 10 && arr(1).value == 0)
    var ii = 1
    set({
      ii += 1
      ii
    }, arr(ii))
    assert(arr(1).value == 5)
  }
}
