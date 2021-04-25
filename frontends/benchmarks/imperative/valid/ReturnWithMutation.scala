object ReturnWithMutation {

  case class Counter(var x: BigInt)
  def increment(c: Counter): BigInt = {
    if (c.x == 100) {
      c.x += 1
      return c.x
      c.x += 1
      0
    } else {
      c.x += 1
      c.x += 2
      c.x
    }
  }

  def test: Unit = {
    val c = Counter(100)
    val x1 = increment(c)
    val x2 = increment(c)
    assert(x1 == 101)
    assert(x2 == 104)
    assert(c.x == 104)
  }
}
