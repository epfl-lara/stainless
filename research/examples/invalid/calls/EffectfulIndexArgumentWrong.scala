import stainless._
import stainless.lang._

object EffectfulIndexArgumentWrong {
  case class Box(var value: BigInt)

  def mutate(b: Box, v: BigInt): Unit = {
    b.value = v
  }

  def f(arr: Array[Box], idx: Array[Int]): Unit = {
    require(arr.length > 10 && idx.length > 0 && idx(0) == 1 && arr(1).value == 0)
    mutate({
      idx(0) = 2
      arr(idx(0))
    }, 5)
    assert(arr(1).value == 5)
  }
}
