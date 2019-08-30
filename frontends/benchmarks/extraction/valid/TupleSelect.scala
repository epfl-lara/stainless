
case class Pair(_1: BigInt, _2: BigInt, _3: BigInt)

object test {

  def prop = {
    val p = Pair(1, 2, 3)
    assert(p._1 == 1)
    assert(p._2 == 2)
    assert(p._3 == 3)

    val q = (1, 2, 3)
    assert(q._1 == 1)
    assert(q._2 == 2)
    assert(q._3 == 3)
  }

}
