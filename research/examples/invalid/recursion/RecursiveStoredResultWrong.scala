import stainless.lang._

object RecursiveStoredResultWrong {
  case class Box(var value: BigInt)
  case class Holder(var box: Box)

  def store(p: Holder, k: BigInt): Box = {
    require(k >= 0)
    decreases(k)
    if (k == 0) {
      val n = Box(1)
      p.box = n
      n
    } else store(p, k - 1)
  }

  def f(p: Holder): Unit = {
    val r = store(p, 2)
    r.value = 5
    assert(p.box.value == 1)
  }
}
