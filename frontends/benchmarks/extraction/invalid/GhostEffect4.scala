import stainless.lang._
import stainless.annotation._

object GhostEffect4 {

  case class Counter(var n: Int, @ghost var count: BigInt)
  case class Box(var hits: Int)

  def next(b: Box): Int = {
    b.hits += 1
    0
  }

  def foo(cs: Array[Counter], b: Box): Unit = {
    require(cs.length > 0)
    cs(next(b)).count = 0
  }

}
