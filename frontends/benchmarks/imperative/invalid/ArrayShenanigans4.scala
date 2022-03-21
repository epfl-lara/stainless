import stainless.lang._
import stainless.annotation._

object ArrayShenanigans4 {
  case class Ref(var x: Int)

  def test(arr: Array[Ref], i: Int, j: Int, cond: Boolean): Unit = {
    require(0 <= i && i < arr.length)
    require(0 <= j && j < arr.length)

    val oldI = arr(i).x
    val arrij = if (cond) arr(i) else arr(j)
    arrij.x = 42
    assert(!cond ==> (arr(i).x == oldI))
  }
}
