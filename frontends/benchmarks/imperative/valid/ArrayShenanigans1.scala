import stainless.lang._
import stainless.annotation._

object ArrayShenanigans1 {
  case class Ref(var x: Int)

  def test(arr: Array[Ref], i: Int, j: Int, k: Int, cond: Boolean): Unit = {
    require(0 <= i && i < arr.length)
    require(0 <= j && j < arr.length)
    require(0 <= k && k < arr.length)

    val oldI = arr(i).x
    val oldJ = arr(j).x
    val oldK = arr(k).x
    val ajk = if (cond) arr(j) else arr(k)
    ajk.x = 42

    assert((i != j && i != k) ==> (arr(i).x == oldI))
    assert((cond && i != j) ==> (arr(i).x == oldI))

    assert((!cond && i != k) ==> (arr(i).x == oldI))
    assert((!cond && j != k) ==> (arr(j).x == oldJ))

    assert((cond && j != k) ==> (arr(k).x == oldK))

    assert(cond ==> (arr(j).x == 42))
    assert(!cond ==> (arr(k).x == 42))
  }
}
