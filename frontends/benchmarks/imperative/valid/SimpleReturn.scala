object SimpleReturn {
  def example0: Int = {
    return 11
  }

  def example1: Int = {
    return 0
    1
  }

  def example2(x: Int): Int = {
    val a = if (x > 0) { return 1 } else { 2 }
    3
  }

  def example3(cond: Boolean): Boolean = {
    val a = if (cond) { return true } else { 1 }
    false
  }

  def example4: Boolean = {
    val x: Int = return false
    true
  }

  def example5(cond: Boolean) : Int = {
    val x: Int = if (cond) return 100 else { 5 }
    x
  }

  def example6(x: Int): Int = {
    require(x < 100)
    var y = x
    y += 1
    if (x == 50) { y += 1; return y }
    else y += 2
    y
  }

  def tests() = {
    assert(example0 == 11)
    assert(example1 == 0)
    assert(example2(10) == 1)
    assert(example2(-10) == 3)
    assert(example3(true))
    assert(!example3(false))
    assert(!example4)
    assert(example5(true) == 100)
    assert(example5(false) == 5)
    assert(example6(50) == 52)
    assert(example6(42) == 45)
  }
}
