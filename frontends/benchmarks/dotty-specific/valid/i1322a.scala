object i1322a {
  type Pair[R] = (R, R)

  extension [R](p: Pair[R])
    def proj1: R = p._1

  def test(p: Pair[Int]): Unit = {
    require(p.proj1 == 42)
    assert(p._1 == 42)
  }
}