object i1301 {
  def p: (Int, Int) = (1, 2)
  val (x, y) = p

  def test: Unit = {
    assert(x == 1 && y == 2)
    assert(p._1 == 1 && p._2 == 2)
  }
}