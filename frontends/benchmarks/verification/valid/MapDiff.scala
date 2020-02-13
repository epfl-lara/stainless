import stainless.lang._

object MapDiff {

  def test(m: Map[Int, Int]): Unit = {
    require(m.contains(1) && m.contains(2) && m.contains(3))
    val m2 = m -- Set(1, 2)
    assert(!m2.contains(1))
    assert(!m2.contains(2))
    assert(m2.contains(3))
    assert(m2(3) == m(3))
  }
}

